module

public meta import Lean.Widget.UserWidget
public meta import Lean.Meta.Tactic.TryThis
public meta import Lean.Server.Rpc.RequestHandling
public meta import Lean.Elab.Task

public meta import Reap.Options
public meta import Reap.Tactic.Generator
public meta import Reap.Tactic.TreeSearch
public meta import Reap.Future.PP
public meta import TreeSearch

public meta section

open Lean Elab Tactic Server

structure TacticWidgetRangeInfo where
  panelRange : Syntax.Range
  editRange : Lsp.Range
  indent : Nat
  column : Nat

def getTacticWidgetRangeInfo? (rangeRef panelRef : Syntax) :
    TacticM (Option TacticWidgetRangeInfo) := do
  let some tacticRange := rangeRef.getRange? | return none
  let map ← getFileMap
  let panelSyntaxRange := panelRef.getRange?.getD tacticRange
  let panelRange : Syntax.Range := {
    start := map.lineStart (map.toPosition panelSyntaxRange.start).line
    stop := map.lineStart ((map.toPosition panelSyntaxRange.stop).line + 1)
  }
  let editRange : Syntax.Range := { start := tacticRange.start, stop := tacticRange.stop }
  let (indent, column) := Lean.Meta.Tactic.TryThis.getIndentAndColumn map tacticRange
  return some {
    panelRange
    editRange := map.utf8RangeToLspRange editRange
    indent
    column
  }

structure ReapMCTSProgressView where
  visitedNodes : Nat
  maxNodes : Nat
  step : Nat
  maxSteps : Nat
  goalType : String
  script : Option String
  done : Bool
  solved : Bool
  status : String
deriving Inhabited, RpcEncodable

structure ReapMCTSProgressRequest where
  id : Nat
deriving RpcEncodable

structure ReapMCTSProgressWidgetProps where
  id : Nat
  initial : ReapMCTSProgressView
  range : Lsp.Range
deriving RpcEncodable

def ReapMCTSProgressView.ofProgress (progress : Reap.TreeSearch.MCTSProgress)
    (script : Option String := none) : ReapMCTSProgressView where
  visitedNodes := progress.visitedNodes
  maxNodes := progress.maxNodes
  step := progress.step
  maxSteps := progress.maxSteps
  goalType := progress.goalType
  script := script
  done := progress.done
  solved := progress.solved
  status := if progress.done && progress.solved then "assembling proof" else progress.status

def ReapMCTSProgressView.initial (maxNodes maxSteps : Nat) : ReapMCTSProgressView :=
  ReapMCTSProgressView.ofProgress <| Reap.TreeSearch.MCTSProgress.initial maxNodes maxSteps

def ReapMCTSProgressView.missing : ReapMCTSProgressView :=
  ReapMCTSProgressView.ofProgress {
    visitedNodes := 0
    maxNodes := 0
    step := 0
    maxSteps := 0
    goalType := "progress unavailable"
    done := true
    solved := false
    status := "missing"
  }

initialize reapMCTSProgressStore : IO.Ref (Nat × List (Nat × ReapMCTSProgressView)) ←
  IO.mkRef (0, [])

def freshReapMCTSProgressId : BaseIO Nat :=
  reapMCTSProgressStore.modifyGet fun (next, entries) => (next, (next + 1, entries))

def setReapMCTSProgress (id : Nat) (progress : ReapMCTSProgressView) : BaseIO Unit :=
  reapMCTSProgressStore.modify fun (next, entries) =>
    (next, (id, progress) :: entries.filter (fun entry => entry.1 != id))

def getReapMCTSProgress? (id : Nat) : BaseIO (Option ReapMCTSProgressView) := do
  let (_, entries) ← reapMCTSProgressStore.get
  return (entries.find? fun entry => entry.1 == id).map fun entry => entry.2

def formatTryThisText (tacRef : Syntax) (text : String) : TacticM String := do
  let text := text.trimAscii.toString
  if let some rangeInfo ← getTacticWidgetRangeInfo? tacRef tacRef then
    return Std.Format.pretty text (indent := rangeInfo.indent) (column := rangeInfo.column)
  else
    return text

@[server_rpc_method]
def getReapMCTSProgress (req : ReapMCTSProgressRequest) :
    RequestM (RequestTask ReapMCTSProgressView) :=
  RequestM.asTask do
    return (← getReapMCTSProgress? req.id).getD ReapMCTSProgressView.missing

@[widget_module] def reapMCTSProgressWidget : Widget.UserWidgetDefinition where
  name := "Reap MCTS progress"
  javascript := "
import * as React from 'react';
import { EditorContext, useRpcSession, mapRpcError } from '@leanprover/infoview';
const e = React.createElement;

function displayProgress(progress) {
  return '[' + (progress.step || 0) + '/' + (progress.maxSteps || 0) + ']';
}

function shouldPoll(progress) {
  return !progress.done || (progress.solved && !progress.script);
}

export default function(props) {
  const rs = useRpcSession();
  const editorConnection = React.useContext(EditorContext);
  const [progress, setProgress] = React.useState(props.initial);
  const [error, setError] = React.useState(null);

  React.useEffect(() => {
    let cancelled = false;
    let timer = null;

    async function poll() {
      try {
        const next = await rs.call('getReapMCTSProgress', { id: props.id });
        if (cancelled) return;
        setProgress(next);
        setError(null);
        if (shouldPoll(next)) {
          timer = window.setTimeout(poll, 300);
        }
      } catch (err) {
        if (cancelled) return;
        setError(mapRpcError(err).message);
        timer = window.setTimeout(poll, 1000);
      }
    }

    poll();
    return () => {
      cancelled = true;
      if (timer !== null) window.clearTimeout(timer);
    };
  }, [rs, props.id]);

  const statusColor = progress.solved
    ? 'var(--vscode-testing-iconPassed)'
    : progress.done
      ? 'var(--vscode-descriptionForeground)'
      : 'var(--vscode-progressBar-background)';
  const goal = progress.goalType || 'starting';
  function onClick() {
    if (!progress.script) return;
    editorConnection.api.applyEdit({
      changes: { [props.pos.uri]: [{ range: props.range, newText: progress.script }] }
    });
  }
  function tryThis() {
    if (!progress.script) return null;
    return e('div',
      {
        className: 'font-code pre-wrap',
        style: {
          marginTop: '0.5em',
          whiteSpace: 'pre-wrap',
          overflowWrap: 'anywhere'
        }
      },
      e('div', null, 'Try this:'),
      e('div', null,
        e('span',
          {
            onClick,
            title: 'Apply suggestion',
            className: 'link pointer dim font-code',
            style: { color: 'var(--vscode-textLink-foreground)' }
          },
          '[apply]'),
        ' ',
        e('span', null, progress.script)))
  }

  return e('div',
    {
      className: 'ml1 font-code pre-wrap',
      style: { overflowWrap: 'anywhere' }
    },
    e('div',
      {
        style: {
          display: 'flex',
          gap: '0.5em',
          alignItems: 'baseline',
          overflowWrap: 'anywhere'
        }
      },
      e('span', { style: { color: statusColor, fontWeight: 600 } }, progress.status || 'running'),
      e('span', { style: { color: statusColor, fontWeight: 600 } }, displayProgress(progress)),
      e('span', null, goal),
      error ? e('span', { style: { color: 'var(--vscode-errorForeground)' } }, error) : null
    ),
    tryThis()
  );
}"

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

def checkTacticSyntax (stx : Syntax) : TacticM <| CheckResult × String := do
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
  catch e =>
    logInfo m!"Number of errors: {(← getNumErrors)}"
    logError m!"Error while checking suggestion 1: {e.toMessageData}"
    pure (CheckResult.Invalid, "error")

/- Check whether the suggestion `s` completes the proof, is valid (does
not result in an error message), or is invalid. -/
def checkTactic (tacticStr: String) : TacticM <| CheckResult × String := do
  withoutModifyingState do
    try
      match Parser.runParserCategory (← getEnv) `tactic tacticStr with
        | Except.ok stx =>
          checkTacticSyntax stx
        | Except.error e =>
          match Parser.runParserCategory (← getEnv) `tactic (Reap.TreeSearch.MCTS.wrapProofScriptAsTactic tacticStr) with
          | Except.ok stx => checkTacticSyntax stx
          | Except.error _ =>
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
  if let some rangeInfo ← getTacticWidgetRangeInfo? (origSpan?.getD tacRef) tacRef then
    let checks ← suggestions.mapM checkTactic
    let texts := suggestions.map fun text =>
      Std.Format.pretty text.trimAscii.toString
        (indent := rangeInfo.indent) (column := rangeInfo.column)
    let textsAndChecks := (texts.zip checks |>.qsort
      fun a b => compare a.2.1 b.2.1 = Ordering.lt).filter fun x =>
        match x.2.1 with
        | CheckResult.ProofDone => true
        | CheckResult.Valid => true
        | CheckResult.Invalid => false
    let tactic := Std.Format.pretty f!"{tacRef.prettyPrint}{tacRef.prettyPrint}"
    let json := Json.mkObj [
      ("tactic", tactic),
      ("suggestions", toJson textsAndChecks),
      ("range", toJson rangeInfo.editRange),
      ("info", extraMsg)
    ]
    Widget.savePanelWidgetInfo
      (hash llmstepTryThisWidget.javascript) (StateT.lift json) (.ofRange rangeInfo.panelRange)


def addMCTSProgressWidget (tacRef : Syntax) (id : Nat)
    (initial : ReapMCTSProgressView) : TacticM Unit := do
  if let some rangeInfo ← getTacticWidgetRangeInfo? tacRef tacRef then
    let props : ReapMCTSProgressWidgetProps :=
      { id, initial, range := rangeInfo.editRange }
    Widget.savePanelWidgetInfo
      (hash reapMCTSProgressWidget.javascript) (rpcEncode props) (.ofRange rangeInfo.panelRange)



def reaperTac (gs : List MVarId) : TacticM Unit := do
  let suggestions ← TacticGenerator.generateTactics gs
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

def reaper!Tac (gs : List MVarId) : TacticM Unit := do
  let suggestions ← TacticGenerator.generateTactics gs
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
def reaper?Tac (gs : List MVarId) : MetaM (Array (String × Float)) :=
  TacticGenerator.generateTactics gs

elab "reap" : tactic => do
    let gs ← getUnsolvedGoals
    reaperTac gs

elab "reapMCTS" : tactic => do
  let opts ← Lean.getOptions
  let maxGoals := reap.max_goals.get opts
  let maxSteps := reap.max_steps.get opts
  Reap.TreeSearch.reapMCTS TacticGenerator.generatePolicyValue maxGoals maxSteps

syntax (name := reapBangBang) "reap!!" : tactic

@[tactic reapBangBang] def evalReapBangBang : Tactic := fun stx => do
  let opts ← Lean.getOptions
  let maxGoals := reap.max_goals.get opts
  let maxSteps := reap.max_steps.get opts
  let progressId ← freshReapMCTSProgressId
  let initialProgress := ReapMCTSProgressView.initial maxGoals maxSteps
  setReapMCTSProgress progressId initialProgress
  addMCTSProgressWidget stx progressId initialProgress
  let markDone (solved : Bool) (status goalType : String) (script : Option String := none) :
      TacticM Unit := do
    let progress := (← getReapMCTSProgress? progressId).getD initialProgress
    setReapMCTSProgress progressId {
      progress with
        done := true
        solved := solved
        status := status
        goalType := goalType
        script := script
    }
  let reportProgress (progress : Reap.TreeSearch.MCTSProgress) : TacticM Unit :=
    setReapMCTSProgress progressId (ReapMCTSProgressView.ofProgress progress)
  let searchTask : TacticM Unit := do
    try
      let saved ← saveState
      let result ← Reap.TreeSearch.runMCTS
        TacticGenerator.generatePolicyValue
        (maxNodes := maxGoals) (maxSteps := maxSteps) (progress? := some reportProgress)
      saved.restore
      match result.solution? with
      | none =>
          markDone false "exhausted" "search exhausted"
      | some nodeIdx =>
          match Reap.TreeSearch.MCTS.proofScriptForSolvedNode result.nodes nodeIdx with
          | .error _ =>
              markDone false "failed" "proof script extraction failed"
          | .ok script =>
              match ← Reap.TreeSearch.checkProofScript result.ctx script with
              | .ok _ =>
                  markDone true "solved" "no goals" (some (← formatTryThisText stx script))
              | .error _ =>
                  markDone false "failed" "final proof check failed"
    catch e =>
      logError e.toMessageData
      markDone false "failed" "search failed"
  discard <| Lean.Elab.Tactic.TacticM.asTask searchTask
