module
public meta import Lean.Elab.Task
public meta import OpenAIClient
public meta import Reap.Options
public meta import Reap.PremiseSelection.Syntax
public meta import Reap.Tactic.WallClock

public meta section

open Lean Elab Tactic
open Reap.WallClock

structure TacticGenerator where
  llmClient : OpenAIClient
  valueClient : OpenAIClient
  premiseSelectionClient : PremiseSelectionClient
  model : String

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

def retryM? {α ε : Type} {m : Type → Type} [Monad m] [MonadExcept ε m]
    (action : m α) (maxRetries : Nat := 3) : m (Option α) := do
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
  let formalStatement := ps.formal_statement
  "Formal name: " ++ formalName ++ "\n" ++
  "Formal statement: " ++ formalStatement

def mkPrompt (tacticState : String) (relatedTheorems: Array PremiseSelectionResult) : String :=
  "User: Please generate a tactic in lean4 to solve the state.
Here're some theorems that may be helpful:
" ++ (relatedTheorems.mapIdx mkRelatedTheorem |>.joinSep "\n") ++
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
    model := reap.model.get (← getOptions)
  }

deriving instance ToJson for OpenAIChatCompletionTokenLogprob, OpenAIChoiceLogprobs, OpenAIChatChoice, OpenAIChatResponse

structure ValueResult where
  score : Float
deriving Inhabited, FromJson, ToJson

def getRelatedTheorems (config : ReapGenerationConfig) (mvarIds : List MVarId) (ppGoal : String) :
    MetaM (Array PremiseSelectionResult) := do
  withLogWallClockTime "premise_select" (fun result => json%{ goal: $ppGoal, result: $result }) do
    selectPremisesForGoals mvarIds config.numPremises

def mkChatRequest (config : ReapGenerationConfig) (model : String) (prompt : String) (n : Nat) :
    OpenAIChatRequest := {
  model
  messages := [ { role := "user", content := prompt } ]
  n := n
  temperature := config.temperature
  max_tokens := config.maxTokens
  logprobs := true
}

def generatePolicyFromPrompt (generator : TacticGenerator) (config : ReapGenerationConfig)
    (ppGoal : String) (relatedTheorems : Array PremiseSelectionResult) (prompt : String) :
    CoreM (Array (String × Float)) := do
  let mut results : List (String × Float) := []
  let req := mkChatRequest config generator.model prompt config.numSamples
  let res ← withLogWallClockTime "tactic_gen" (fun result => json%{ goal: $ppGoal, ps: $relatedTheorems, result: $result }) <|
    retryM? (generator.llmClient.generateChat req)
  if let some res := res then
    for result in (parseChatResponseOpenAI res) do
      results := results.insert result
    results := results.eraseDupsBy (fun x y => x.1 == y.1)
    return results.toArray
  else
    return #[]

def generateValueFromPrompt (generator : TacticGenerator) (config : ReapGenerationConfig)
    (ppGoal : String) (relatedTheorems : Array PremiseSelectionResult) (prompt : String) :
    CoreM Float := do
  let req := mkChatRequest config generator.model prompt 1
  let result : Option ValueResult ← withLogWallClockTime "value" (fun result => json%{ state: $ppGoal, ps: $relatedTheorems, result: $result }) do
    retryM? (maxRetries := 3) do
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
def generatePPTactics (config : ReapGenerationConfig) (mvarIds : List MVarId) (ppGoal : String) :
    MetaM (Array PremiseSelectionResult × Array (String × Float)) := do
  let generator ← getClient
  let relatedTheorems ← getRelatedTheorems config mvarIds ppGoal
  let prompt := mkPrompt ppGoal relatedTheorems
  let tactics ← generatePolicyFromPrompt generator config ppGoal relatedTheorems prompt
  return (relatedTheorems, tactics)

def Meta.ppProofState (mvarIds : List MVarId) : MetaM Format := do
  return Std.Format.joinSep (← mvarIds.mapM (Meta.ppGoal)) "\n".toFormat


def generateTactics (config : ReapGenerationConfig) (mvarIds : List MVarId) :
    MetaM <| Array (String × Float) := do
  let ppProofState := toString (← Meta.ppProofState mvarIds)
  return (← generatePPTactics config mvarIds ppProofState).2

def generateTacticsWithPremises (config : ReapGenerationConfig) (mvarIds : List MVarId) :
    MetaM <| Array (String × Array PremiseSelectionResult × Float) := do
  let ppProofState := toString (← Meta.ppProofState mvarIds)
  let (ps, res) ← generatePPTactics config mvarIds ppProofState
  return res.map fun (x, y) => (x, ps, y)

def generateValue (config : ReapGenerationConfig) (mvarIds : List MVarId) : MetaM Float := do
  let generator ← getClient
  let ppProofState := toString (← Meta.ppProofState mvarIds)
  let relatedTheorems ← getRelatedTheorems config mvarIds ppProofState
  let prompt := mkPrompt ppProofState relatedTheorems
  generateValueFromPrompt generator config ppProofState relatedTheorems prompt

def generatePolicyValue (config : ReapGenerationConfig) (mvarIds : List MVarId) :
    MetaM <| Float × Array (String × Array PremiseSelectionResult × Float) := do
  let generator ← getClient
  let ppProofState := toString (← Meta.ppProofState mvarIds)
  let relatedTheorems ← getRelatedTheorems config mvarIds ppProofState
  let prompt := mkPrompt ppProofState relatedTheorems
  let (_, valueTask) ← Lean.Core.CoreM.asTask <|
    generateValueFromPrompt generator config ppProofState relatedTheorems prompt
  let (_, policyTask) ← Lean.Core.CoreM.asTask <|
    generatePolicyFromPrompt generator config ppProofState relatedTheorems prompt
  let value ← valueTask.get
  let tactics ← policyTask.get
  return (value, tactics.map fun (x, y) => (x, relatedTheorems, y))
