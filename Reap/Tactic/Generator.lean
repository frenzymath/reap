module
public meta import OpenAIClient
public meta import Reap.Options
public meta import Reap.Future.Basic
public meta import Reap.PremiseSelection.API

public meta section

open Lean Elab Tactic

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
  let s := s.trimLeft
  if s.startsWith "<think>" then
    let parts := s.splitOn "</think>"
    if parts.length > 1 then
      (String.intercalate "</think>" (parts.drop 1)).trimLeft
    else s
  else s

def filterGeneration (s: String) : Bool :=
  let banned := ["sorry", "admit", "▅", "apply?", "exact?", "refine?", "calc?", "hint"]
  !(banned.any fun s' => (s.splitOn s').length > 1)

def parseCompletionResponseOpenAI (res: OpenAICompletionResponse) : Array String :=
  (res.choices.map fun x => (x.text)).toArray

def parseChatResponseOpenAI (res: OpenAIChatResponse) : Array (String × Float) :=
  (res.choices.map fun x => (stripThinkingPrefix x.message.content, x.computeLogProbability)).toArray

def mkValuePrompt (tacticState : String) : String :=
  "Please estimate how many tactic steps are required to solve this proof state in Lean.
STATE:
" ++ tacticState

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
    llmClient := ⟨reap.llm_endpoint.get (← getOptions), reap.llm_api_key.get (← getOptions)⟩
    valueClient := ⟨reap.value_endpoint.get (← getOptions), reap.llm_api_key.get (← getOptions)⟩
    premiseSelectionClient := ⟨reap.ps_endpoint.get (← getOptions)⟩
  }

/-- Main function to generate tactics -/
def generatePPTactics (ppGoal : String) : CoreM <| Array (String × Float) := do
  let generator ← getClient
  let relatedTheorems ←
    PremiseSelectionClient.getPremises ppGoal (reap.num_premises.get (← getOptions))
  let prompt := mkPrompt ppGoal relatedTheorems
  -- let mut results : Std.HashSet String := Std.HashSet.emptyWithCapacity
  let mut results : List (String × Float) := []
  let req : OpenAIChatRequest := {
    model := reap.model.get (← getOptions),
    messages := [ { role := "user", content := prompt } ],
    n := reap.num_samples.get (← getOptions),
    temperature := (reap.temperature.get (← getOptions)).toFloat / 100.0,
    max_tokens := reap.max_tokens.get (← getOptions),
    logprobs := true
  }
  let res ← generator.llmClient.generateChat req
  for result in (parseChatResponseOpenAI res) do
    results := results.insert result
    -- logInfo m!"Generated tactic: {result.1} with probability {result.2}"
  results := results.eraseDupsBy (fun x y => x.1 == y.1)
  let finalResults := (results.toArray.filter fun x => filterGeneration x.1)
  -- let finalResults := (results.toArray.filter filterGeneration).map fun x => (x, 1.0)
  return finalResults

def Meta.ppProofState (mvarIds : List MVarId) : MetaM Format := do
  return Std.Format.joinSep (← mvarIds.mapM (Meta.ppGoal)) "\n".toFormat


def generateTactics (mvarIds : List MVarId) : MetaM <| Array (String × Float) := do
  let ppProofState := toString (← Meta.ppProofState mvarIds)
  generatePPTactics ppProofState

structure ValueResult where
  score : Float
deriving Inhabited, FromJson

def generateValue (mvarIds : List MVarId) : MetaM Float := do
  let generator ← getClient
  let ppProofState := toString (← Meta.ppProofState mvarIds)
  let prompt := mkValuePrompt ppProofState
  let req : OpenAIChatRequest := {
    model := reap.model.get (← getOptions),
    messages := [ { role := "user", content := prompt } ],
    n := 1,
    temperature := (reap.temperature.get (← getOptions)).toFloat / 100.0,
    max_tokens := reap.max_tokens.get (← getOptions),
    logprobs := true
  }
  let mut result : Option ValueResult := none
  let mut i := 0
  while result.isNone && i < 3 do
    -- try
    i := i + 1
    let res ← generator.valueClient.generateChat req
    let res := parseChatResponseOpenAI res
    let res := Json.parse res[0]!.1
    if let .ok res := res then
      result := fromJson? res |>.toOption
  return -result.get!.score
