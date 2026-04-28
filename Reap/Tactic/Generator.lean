module
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

/-- Remove a few common non-tactic prefixes emitted by generic chat models. -/
def normalizeGeneration (s : String) : String :=
  let s := stripThinkingPrefix s
  let s := s.trimAsciiStart.toString
  if s.startsWith "<;>" then
    (String.intercalate "<;>" ((s.splitOn "<;>").drop 1)).trimAsciiStart.toString
  else
    s

def filterGeneration (s: String) : Bool :=
  let banned := ["sorry", "admit", "▅", "apply?", "exact?", "refine?", "calc?", "hint"]
  !(banned.any fun s' => (s.splitOn s').length > 1)

def retryCoreM? (action : CoreM α) (maxRetries : Nat := 3) : CoreM (Option α) := do
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
  (res.choices.map fun x => (normalizeGeneration x.message.content, x.computeLogProbability)).toArray

def normalizeCandidatePriors (xs : Array (String × Float)) : Array (String × Float) :=
  if xs.isEmpty then
    #[]
  else
    let maxLogprob := xs.foldl (init := xs[0]!.2) fun acc (_, logprob) => max acc logprob
    let weights := xs.map fun (_, logprob) => Float.exp (logprob - maxLogprob)
    let total := weights.foldl (init := (0.0 : Float)) fun acc weight => acc + weight
    if total <= (0.0 : Float) then
      let uniform := 1.0 / xs.size.toFloat
      xs.map fun (tactic, _) => (tactic, uniform)
    else
      (xs.zipIdx.map fun | ((tactic, _), i) => (tactic, weights[i]! / total))

def mkRelatedTheorem (id: Nat) (ps : PremiseSelectionResult) : String :=
  let formalName := ps.formal_name
  let informalName := ps.informal_name
  let formalStatement := ps.formal_statement
  "ID: " ++ toString id ++ "\n" ++
  "Formal name: " ++ formalName ++ "\n" ++
  "Informal name: " ++ informalName ++ "\n" ++
  "Formal statement: " ++ formalStatement

def mkPrompt (tacticState : String) (relatedTheorems: Array PremiseSelectionResult) : String :=
  "User: Please generate a tactic in lean4 to solve the state.
Here're some theorems that may be helpful:
" ++ (Array.mapIdx' mkRelatedTheorem relatedTheorems |>.joinSep "\n") ++ "
STATE:
" ++ tacticState ++ "
TACTIC:

Assistant:"

def mkValuePrompt (tacticState : String) (relatedTheorems: Array PremiseSelectionResult) : String :=
  mkPrompt tacticState relatedTheorems

def getClient : CoreM TacticGenerator := do
  return {
    llmClient := ⟨reap.policy_endpoint.get (← getOptions), reap.llm_api_key.get (← getOptions)⟩
    valueClient := ⟨reap.value_endpoint.get (← getOptions), reap.llm_api_key.get (← getOptions)⟩
    premiseSelectionClient := ⟨reap.ps_endpoint.get (← getOptions)⟩
  }

/-- Main function to generate tactics -/
def generatePPTactics (ppGoal : String) : CoreM (Array PremiseSelectionResult × Array (String × Float)) := do
  let opts ← getOptions
  withCumulativeWallClockTime "reap.wall.tactic_gen" do
    let generator ← getClient
    let relatedTheorems ←
      PremiseSelectionClient.getPremises ppGoal (reap.num_premises.get opts)
    let prompt := mkPrompt ppGoal relatedTheorems
    -- let mut results : Std.HashSet String := Std.HashSet.emptyWithCapacity
    let mut results : List (String × Float) := []
    let req : OpenAIChatRequest := {
      model := reap.model.get opts,
      messages := [ { role := "user", content := prompt } ],
      n := reap.num_samples.get opts,
      temperature := (reap.temperature.get opts).toFloat / 100.0,
      max_tokens := reap.max_tokens.get opts,
      logprobs := true
    }
    let some res ← retryCoreM? (generator.llmClient.generateChat req) | return (#[], #[])
    for result in (parseChatResponseOpenAI res) do
      results := results.insert result
      -- logInfo m!"Generated tactic: {result.1} with probability {result.2}"
    results := results.eraseDupsBy (fun x y => x.1 == y.1)
    let finalResults :=
      normalizeCandidatePriors <| (results.toArray.filter fun x => filterGeneration x.1)
    -- let finalResults := (results.toArray.filter filterGeneration).map fun x => (x, 1.0)
    return (relatedTheorems, finalResults)

def Meta.ppProofState (mvarIds : List MVarId) : MetaM String := do
  let goals ← mvarIds.mapM fun mvarId => do
    let ppGoal := toString (← Meta.ppGoal mvarId)
    return ppGoal
  return String.intercalate "\n\n" goals


def generateTactics (mvarIds : List MVarId) : MetaM <| Array (String × Float) := do
  let ppProofState ← Meta.ppProofState mvarIds
  return (← generatePPTactics ppProofState).2

def generateTacticsWithPremises (mvarIds : List MVarId) : MetaM <| Array (String × Array PremiseSelectionResult × Float) := do
  let ppProofState ← Meta.ppProofState mvarIds
  let (ps, res) ← generatePPTactics ppProofState
  return res.map fun (x, y) => (x, ps, y)

structure ValueResult where
  score : Float
deriving Inhabited, FromJson

def generateValue (mvarIds : List MVarId) : MetaM Float := do
  let opts ← getOptions
  withCumulativeWallClockTime "reap.wall.value" do
    let generator ← getClient
    let ppProofState ← Meta.ppProofState mvarIds
    let relatedTheorems ←
      PremiseSelectionClient.getPremises ppProofState (reap.num_premises.get opts)
    let prompt := mkValuePrompt ppProofState relatedTheorems
    let req : OpenAIChatRequest := {
      model := reap.model.get opts,
      messages := [ { role := "user", content := prompt } ],
      n := 1,
      temperature := (reap.temperature.get opts).toFloat / 100.0,
      max_tokens := reap.max_tokens.get opts,
      logprobs := true
    }
    let result : Option ValueResult ← retryCoreM? (maxRetries := 3) do
      let res ← generator.valueClient.generateChat req
      let res := parseChatResponseOpenAI res
      let res := Json.parse res[0]!.1
      if let .ok res := res then
        match fromJson? res with
        | .ok value => return value
        | .error _ => throwError "Failed to decode value response"
      else
        throwError "Failed to parse value response as JSON"
    return result.get!.score
