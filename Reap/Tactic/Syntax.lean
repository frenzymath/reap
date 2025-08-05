import Lean.Widget.UserWidget

import Reap.Tactic.Basic
import Reap.Tactic.Generator
import Reap.Future.PP

open Lean Elab Tactic

/-  This function is modified from LLMLean.
    Display clickable suggestions in the VSCode Lean Infoview.
    When a suggestion is clicked, this widget replaces the `llmstep` call
    with the suggestion, and saves the call in an adjacent comment.
    Code based on `Std.Tactic.TryThis.tryThisWidget`. -/
@[widget_module] def llmstepTryThisWidget : Widget.UserWidgetDefinition where
  name := "Reap suggestions"
  javascript := "
import * as React from 'react';
import { EditorContext } from '@leanprover/infoview';
const e = React.createElement;
export default function(props) {
  const editorConnection = React.useContext(EditorContext)
  function onClick(suggestion) {
    editorConnection.api.applyEdit({
      changes: { [props.pos.uri]: [{ range:
        props.range,
        newText: suggestion[0]
        }] }
    })
  }
  const suggestionElement = props.suggestions.length > 0
    ? [
      'Try this: ',
      ...(props.suggestions.map((suggestion, i) =>
          [e('li', {onClick: () => onClick(suggestion),
            className:
              suggestion[1][0] === 'ProofDone' ? 'link pointer dim green' :
              suggestion[1][0] === 'Valid' ? 'link pointer dim blue' :
              'link pointer dim',
            title: 'Apply suggestion'},
            suggestion[1][0] === 'ProofDone' ? '🎉 ' + suggestion[0] : suggestion[0]
        ), e('div', null, suggestion[1][1])]
      )),
      props.info
    ]
    : 'No valid suggestions.';
  return e('div',
  {className: 'ml1'},
  e('ul', {className: 'font-code pre-wrap'},
  suggestionElement))
}"

inductive CheckResult : Type
  | ProofDone
  | Valid
  | Invalid
  deriving ToJson, Ord, Repr, Inhabited

instance : ToString CheckResult where
  toString
    | CheckResult.ProofDone => "ProofDone"
    | CheckResult.Valid => "Valid"
    | CheckResult.Invalid => "Invalid"
-- def runSuggestUntilFailure (generator : ) (proofState : List MVarId) : TacticM <| List <| List MVarId := sorry

def getNumErrors : CoreM Nat := do
  let log := (← getThe Core.State).messages
  return (log.unreported.map fun m =>
    if m.severity matches .error then 1 else 0).foldl (fun a b => a + b) 0

/- Check whether the suggestion `s` completes the proof, is valid (does
not result in an error message), or is invalid. -/
def checkTactic (tacticStr: String) : TacticM <| CheckResult × String := do
  withoutModifyingState do
    try
      match Parser.runParserCategory (← getEnv) `tactic tacticStr with
        | Except.ok stx =>
          -- logInfo m!"Checking suggestion: {s}"
          try
            _ ← evalTactic stx
            let goals ← getUnsolvedGoals

            if (← getThe Core.State).messages.hasErrors then
              pure (CheckResult.Invalid, "error")
            else if goals.isEmpty then
              pure (CheckResult.ProofDone, "no goals")
            else
              let goal ← getMainGoal
              Elab.Tactic.withMainContext do
              pure (CheckResult.Valid, toString <| ← Meta.ppGoalType goal)
              -- pure (CheckResult.Valid, "")
          catch e =>
            -- logInfo m!"All messages: {(← getThe Core.State).messages.unreported}"
            logInfo m!"Number of errors: {(← getNumErrors)}"
            logError m!"Error while checking suggestion 1: {e.toMessageData}"
            pure (CheckResult.Invalid, "error")
        | Except.error e =>
          logError m!"Error while parsing suggestion 2: {e}"
          pure (CheckResult.Invalid, "error")
    catch e =>
      logError m!"Error while evaluating suggestion 3: {e.toMessageData}"
      pure (CheckResult.Invalid, "error")


/- Adds multiple suggestions to the Lean InfoView.
   Code based on `Std.Tactic.addSuggestion`. -/
def addSuggestions (tacRef : Syntax) (suggestions: Array (String × Float))
    (origSpan? : Option Syntax := none)
    (extraMsg : String := "") : TacticM Unit := do
  let suggestions := suggestions.map fun ⟨x, _⟩ => x
  if let some tacticRange := (origSpan?.getD tacRef).getRange? then
    -- if let some argRange := (origSpan?.getD pfxRef).getRange? then
      let map ← getFileMap
      let start := String.findLineStart map.source tacticRange.start
      let body := map.source.findAux (· ≠ ' ') tacticRange.start start

      let checks ← suggestions.mapM checkTactic
      let texts := suggestions.map fun text => (
        (Std.Format.pretty text.trim
         (indent := (body - start).1)
         (column := (tacticRange.start - start).1)
      ))
      let textsAndChecks := (texts.zip checks |>.qsort
        fun a b => compare a.2.1 b.2.1 = Ordering.lt).filter fun x =>
          match x.2.1 with
          | CheckResult.ProofDone => true
          | CheckResult.Valid => true
          | CheckResult.Invalid => false

      let start := (tacRef.getRange?.getD tacticRange).start
      let stop := (tacRef.getRange?.getD tacticRange).stop
      let stxRange :=

      { start := map.lineStart (map.toPosition start).line
        stop := map.lineStart ((map.toPosition stop).line + 1) }
      let full_range : String.Range :=
      { start := tacticRange.start, stop := tacticRange.stop }
      let full_range := map.utf8RangeToLspRange full_range
      let tactic := Std.Format.pretty f!"{tacRef.prettyPrint}{tacRef.prettyPrint}"
      let json := Json.mkObj [
        ("tactic", tactic),
        ("suggestions", toJson textsAndChecks),
        ("range", toJson full_range),
        ("info", extraMsg)
      ]
      Widget.savePanelWidgetInfo (hash llmstepTryThisWidget.javascript) (StateT.lift json) (.ofRange stxRange)

def options : TacticGeneratorOptions := {
  ps_endpoint := return tacticgenerator.ps_endpoint.get (← getOptions)
  llm_endpoint := return tacticgenerator.llm_endpoint.get (← getOptions)
  llm_api_key := return tacticgenerator.llm_api_key.get (← getOptions)
  temperature := return 0.7
  num_samples := return tacticgenerator.num_samples.get (← getOptions)
  num_premises := return tacticgenerator.num_premises.get (← getOptions)
  max_tokens := return tacticgenerator.max_tokens.get (← getOptions)
  model := return tacticgenerator.model.get (← getOptions)}

def getClient : CoreM TacticGenerator := do
  return {
    llmClient := ⟨← options.llm_endpoint, ← options.llm_api_key⟩
    premiseSelectionClient := ⟨← options.ps_endpoint⟩
  }

def reaperTac (g : MVarId) : TacticM Unit := do
  let pp := toString (← Meta.ppGoal g)
  let tacticGenerator ← getClient
  let suggestions ← tacticGenerator.generateTactics pp options
  if suggestions.isEmpty then
    logInfo m!"No suggestions generated."
  else
    let suggestionsWithChecks := (← suggestions.mapM fun s => do
      let (check, info) ← checkTactic s.1
      return (s.1, (check, info)))
    let validSuggestions := suggestionsWithChecks.filter fun x =>
      let check := x.2.1
      match check with
      | .ProofDone => true
      | .Valid => true
      | .Invalid => false
    if validSuggestions.isEmpty then
      throwError "No valid suggestions generated."
    else
      let firstSugg := validSuggestions[0]!.1
      match Parser.runParserCategory (← getEnv) `tactic firstSugg with
      | Except.ok stx =>
        -- logInfo m!"Applying suggestion: {firstSugg}"
        evalTactic stx
      | Except.error e =>
        throwError "Error while parsing suggestion: {e}"

def reaper!Tac (g : MVarId) : TacticM Unit := do
  let pp := toString (← Meta.ppGoal g)
  let tacticGenerator ← getClient
  let suggestions ← tacticGenerator.generateTactics pp options
  if suggestions.isEmpty then
    logInfo m!"No suggestions generated."
  else
    let suggestionsWithChecks := (← suggestions.mapM fun s => do
      let (check, info) ← checkTactic s.1
      return (s.1, (check, info)))
    let validSuggestions := suggestionsWithChecks.filter fun x =>
      let check := x.2.1
      match check with
      | .ProofDone => true
      | .Valid => false
      | .Invalid => false
    if validSuggestions.isEmpty then
      throwError "No valid suggestions generated."
    else
      let firstSugg := validSuggestions[0]!.1
      match Parser.runParserCategory (← getEnv) `tactic firstSugg with
      | Except.ok stx =>
        -- logInfo m!"Applying suggestion: {firstSugg}"
        evalTactic stx
      | Except.error e =>
        throwError "Error while parsing suggestion: {e}"
/--
Call the LLM on a goal, asking for suggestions beginning with a prefix.
-/
def reaper?Tac (g : MVarId) : MetaM (Array (String × Float)) := do
  let pp := toString (← Meta.ppGoal g)
  let tacticGenerator ← getClient
  tacticGenerator.generateTactics pp options

syntax "reap" : tactic
elab_rules : tactic
  | `(tactic | reap) => do
    let g ← getMainGoal
    reaperTac g

syntax "reap?" : tactic
elab_rules : tactic
  | `(tactic | reap?%$tac) => do
    addSuggestions tac (← liftMetaMAtMain reaper?Tac)

syntax "reap!" : tactic
elab_rules : tactic
  | `(tactic | reap!) => do
    let g ← getMainGoal
    reaper!Tac g
