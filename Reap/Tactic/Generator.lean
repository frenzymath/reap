module
public meta import Lean.Elab.Task
public meta import OpenAIClient
public meta import Reap.Options
public meta import Reap.Future.Basic
public meta import Reap.PremiseSelection.API
public meta import Reap.Tactic.WallClock

public meta section

open Lean Elab Tactic
open Reap.WallClock

structure TacticGenerator where
  llmClient : OpenAIClient
  valueClient : OpenAIClient
  premiseSelectionClient : PremiseSelectionClient

def OpenAIChatChoice.computeLogProbability (choice: OpenAIChatChoice) : Float :=
  match choice.logprobs with
  | none => 0.0
  | some choice_logprobs =>
    match choice_logprobs.content with
    | none => 0.0
    | some logProbs => (logProbs.map fun x => x.logprob).sum

def OpenAIChatChoice.computeProbability (choice: OpenAIChatChoice) : Float :=
  Float.exp $ OpenAIChatChoice.computeLogProbability choice

namespace TacticGenerator

/-- Strip `<think>...</think>` prefix that some LLMs prepend to their responses. -/
def stripThinkingPrefix (s : String) : String :=
  let s := s.trimAsciiStart.toString
  if s.startsWith "<think>" then
    let parts := s.splitOn "</think>"
    if parts.length > 1 then
      (String.intercalate "</think>" (parts.drop 1)).trimAsciiStart.toString
    else s
  else s

def retryCoreM? {α : Type _} (action : CoreM α) (maxRetries : Nat := 3) : CoreM (Option α) := do
  let mut result : Option α := none
  let mut i := 0
  while result.isNone && i < maxRetries do
    i := i + 1
    try
      result := some (← action)
    catch _ =>
      pure ()
  return result

def parseCompletionResponseOpenAI (res: OpenAICompletionResponse) : Array String :=
  (res.choices.map fun x => (x.text)).toArray

def parseChatResponseOpenAI (res: OpenAIChatResponse) : Array (String × Float) :=
  (res.choices.map fun x => (stripThinkingPrefix x.message.content, x.computeLogProbability)).toArray

def mkRelatedTheorem (_id: Nat) (ps : PremiseSelectionResult) : String :=
  let formalName := ps.formal_name
  -- let informalName := ps.informal_name
  let formalStatement := ps.formal_statement
  -- "ID: " ++ toString id ++ "\n" ++
  "Formal name: " ++ formalName ++ "\n" ++
  -- "Informal name: " ++ informalName ++ "\n" ++
  "Formal statement: " ++ formalStatement

def mkPrompt (tacticState : String) (relatedTheorems: Array PremiseSelectionResult) : String :=
  "User: Please generate a tactic in lean4 to solve the state.
Here're some theorems that may be helpful:
" ++ (Array.mapIdx' mkRelatedTheorem relatedTheorems |>.joinSep "\n") ++
"
STATE:
" ++ tacticState ++ "
TACTIC:

Assistant:"

def getClient : CoreM TacticGenerator := do
  return {
    llmClient := ⟨reap.policy_endpoint.get (← getOptions), reap.llm_api_key.get (← getOptions)⟩
    valueClient := ⟨reap.value_endpoint.get (← getOptions), reap.llm_api_key.get (← getOptions)⟩
    premiseSelectionClient := ⟨reap.ps_endpoint.get (← getOptions)⟩
  }

deriving instance ToJson for OpenAIChatCompletionTokenLogprob, OpenAIChoiceLogprobs, OpenAIChatChoice, OpenAIChatResponse

structure ValueResult where
  score : Float
deriving Inhabited, FromJson, ToJson

def getRelatedTheorems (ppGoal : String) (opts : Options) : CoreM (Array PremiseSelectionResult) := do
  withLogWallClockTime "premise_select" (fun result => json%{ goal: $ppGoal, result: $result }) do
    pure <|
      (← retryCoreM?
        (PremiseSelectionClient.getPremises ppGoal (reap.num_premises.get opts))).getD #[]

def mkChatRequest (opts : Options) (prompt : String) (n : Nat) : OpenAIChatRequest := {
  model := reap.model.get opts
  messages := [ { role := "user", content := prompt } ]
  n := n
  temperature := (reap.temperature.get opts).toFloat / 100.0
  max_tokens := reap.max_tokens.get opts
  logprobs := true
}

def generatePolicyFromPrompt (generator : TacticGenerator) (opts : Options)
    (ppGoal : String) (relatedTheorems : Array PremiseSelectionResult) (prompt : String) :
    CoreM (Array (String × Float)) := do
  -- let mut results : Std.HashSet String := Std.HashSet.emptyWithCapacity
  let mut results : List (String × Float) := []
  let req := mkChatRequest opts prompt (reap.num_samples.get opts)
  let res ← withLogWallClockTime "tactic_gen" (fun result => json%{ goal: $ppGoal, ps: $relatedTheorems, result: $result }) <|
    retryCoreM? (generator.llmClient.generateChat req)
  if let some res := res then
    for result in (parseChatResponseOpenAI res) do
      results := results.insert result
    results := results.eraseDupsBy (fun x y => x.1 == y.1)
    return results.toArray
  else
    return #[]

def generateValueFromPrompt (generator : TacticGenerator) (opts : Options)
    (ppGoal : String) (relatedTheorems : Array PremiseSelectionResult) (prompt : String) :
    CoreM Float := do
  let req := mkChatRequest opts prompt 1
  let result : Option ValueResult ← withLogWallClockTime "value" (fun result => json%{ state: $ppGoal, ps: $relatedTheorems, result: $result }) do
    retryCoreM? (maxRetries := 3) do
      let res ← generator.valueClient.generateChat req
      let res := parseChatResponseOpenAI res
      let res := Json.parse res[0]!.1
      if let .ok res := res then
        match fromJson? res with
        | .ok value => return value
        | .error _ => throwError "Failed to decode value response"
      else
        throwError "Failed to parse value response as JSON"
  match result with
  | some result => return -result.score
  | none => return -1000.0

/-- Main function to generate tactics -/
def generatePPTactics (ppGoal : String) : CoreM (Array PremiseSelectionResult × Array (String × Float)) := do
  let opts ← getOptions
  let generator ← getClient
  let relatedTheorems ← getRelatedTheorems ppGoal opts
  let prompt := mkPrompt ppGoal relatedTheorems
  let tactics ← generatePolicyFromPrompt generator opts ppGoal relatedTheorems prompt
  return (relatedTheorems, tactics)

def Meta.ppProofState (mvarIds : List MVarId) : MetaM Format := do
  return Std.Format.joinSep (← mvarIds.mapM (Meta.ppGoal)) "\n".toFormat


def generateTactics (mvarIds : List MVarId) : MetaM <| Array (String × Float) := do
  let ppProofState := toString (← Meta.ppProofState mvarIds)
  return (← generatePPTactics ppProofState).2

def generateTacticsWithPremises (mvarIds : List MVarId) : MetaM <| Array (String × Array PremiseSelectionResult × Float) := do
  let ppProofState := toString (← Meta.ppProofState mvarIds)
  let (ps, res) ← generatePPTactics ppProofState
  return res.map fun (x, y) => (x, ps, y)

def generateValue (mvarIds : List MVarId) : MetaM Float := do
  let opts ← getOptions
  let generator ← getClient
  let ppProofState := toString (← Meta.ppProofState mvarIds)
  let relatedTheorems ← getRelatedTheorems ppProofState opts
  let prompt := mkPrompt ppProofState relatedTheorems
  generateValueFromPrompt generator opts ppProofState relatedTheorems prompt

def generatePolicyValue (mvarIds : List MVarId) :
    MetaM <| Float × Array (String × Array PremiseSelectionResult × Float) := do
  let opts ← getOptions
  let generator ← getClient
  let ppProofState := toString (← Meta.ppProofState mvarIds)
  let relatedTheorems ← getRelatedTheorems ppProofState opts
  let prompt := mkPrompt ppProofState relatedTheorems
  let (_, valueTask) ← Lean.Core.CoreM.asTask <|
    generateValueFromPrompt generator opts ppProofState relatedTheorems prompt
  let (_, policyTask) ← Lean.Core.CoreM.asTask <|
    generatePolicyFromPrompt generator opts ppProofState relatedTheorems prompt
  let value ← valueTask.get
  let tactics ← policyTask.get
  return (value, tactics.map fun (x, y) => (x, relatedTheorems, y))
