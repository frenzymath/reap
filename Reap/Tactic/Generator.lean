import OpenAIClient
import Reap.Future.Basic
import Reap.PremiseSelection.API

open Lean Elab Tactic

structure TacticGenerator where
  llmClient : OpenAIClient
  premiseSelectionClient : PremiseSelectionClient

structure TacticGeneratorOptions where
  ps_endpoint : CoreM String
  llm_endpoint : CoreM String
  llm_api_key : CoreM String
  temperature : CoreM Float
  num_samples : CoreM Nat
  num_premises : CoreM Nat
  max_tokens : CoreM Nat
  model : CoreM String

namespace TacticGenerator

def filterGeneration (s: String) : Bool :=
  let banned := ["sorry", "admit", "▅"]
  !(banned.any fun s' => (s.splitOn s').length > 1)

def parseCompletionResponseOpenAI (res: OpenAICompletionResponse) : Array String :=
  (res.choices.map fun x => (x.text)).toArray

def parseChatResponseOpenAI (res: OpenAIChatResponse) : Array String :=
  (res.choices.map fun x => (x.message.content)).toArray

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
" ++ (Array.mapIdx' mkRelatedTheorem relatedTheorems |>.joinSep "\n") ++
"
STATE:
" ++ tacticState ++ "
TACTIC:

Assistant:"

/-- Main function to generate tactics -/
def generateTactics (generator : TacticGenerator) (ppGoal : String)
  (options : TacticGeneratorOptions) : CoreM <| Array (String × Float) := do
  let relatedTheorems ←
    generator.premiseSelectionClient.getResults ppGoal (← options.num_premises)
  let prompt := mkPrompt ppGoal relatedTheorems
  let mut results : Std.HashSet String := Std.HashSet.empty
  let req : OpenAIChatRequest := {
    model := ← options.model,
    messages := [ { role := "user", content := prompt } ],
    n := ← options.num_samples,
    temperature := ← options.temperature,
    max_tokens := ← options.max_tokens,
  }
  let res ← generator.llmClient.generateChat req
  for result in (parseChatResponseOpenAI res) do
    results := results.insert result
  let finalResults := (results.toArray.filter filterGeneration).map fun x => (x, 1.0)
  return finalResults


