import Reap.Tactic.Syntax

open Lean Meta Elab Tactic
open Reap.TreeSearch

set_option linter.unusedSimpArgs false

example : True := by
  run_tac do
    let reapStx ←
      match ← parseTacticStr "reap (config := { limits := { total := { maxGoals := 17, maxSteps := 23 }, step := { heartbeats := 29, timeout := 31 } }, generation := { numSamples := 7, numPremises := 11, maxTokens := 37, temperature := 0.41 }, mcts := { cBase := 43.0, cInit := 0.047, visitDiscount := 0.953, priorTemperature := 59.0, progressiveSamplingC := 0.061, progressiveSamplingAlpha := 0.67 } })" with
      | .ok stx => pure stx
      | .error err => throwError "failed to parse reap configuration: {toString err}"
    let closingConfig ← elabReapConfig reapStx[1]
    unless closingConfig.limits.total.maxGoals == 17 && closingConfig.limits.total.maxSteps == 23 &&
        closingConfig.limits.step.heartbeats == 29 && closingConfig.limits.step.timeout == 31 &&
        closingConfig.generation.numSamples == 7 && closingConfig.generation.numPremises == 11 &&
        closingConfig.generation.maxTokens == 37 && closingConfig.generation.temperature == 0.41 &&
        closingConfig.mcts.cBase == 43.0 && closingConfig.mcts.cInit == 0.047 &&
        closingConfig.mcts.visitDiscount == 0.953 && closingConfig.mcts.priorTemperature == 59.0 &&
        closingConfig.mcts.progressiveSamplingC == 0.061 && closingConfig.mcts.progressiveSamplingAlpha == 0.67 do
      throwError "reap configuration was not elaborated correctly"
    let tryThisStx ←
      match ← parseTacticStr "reap? (limits.total.maxGoals := 71) (limits.total.maxSteps := 73) (generation.numSamples := 79) (generation.numPremises := 83) (mcts.cInit := 0.089) (mcts.priorTemperature := 97.0)" with
      | .ok stx => pure stx
      | .error err => throwError "failed to parse reap? configuration: {toString err}"
    let tryThisConfig ← elabReapConfig tryThisStx[1]
    unless tryThisConfig.limits.total.maxGoals == 71 && tryThisConfig.limits.total.maxSteps == 73 &&
        tryThisConfig.generation.numSamples == 79 && tryThisConfig.generation.numPremises == 83 &&
        tryThisConfig.mcts.cInit == 0.089 && tryThisConfig.mcts.priorTemperature == 97.0 do
      throwError "reap? configuration was not elaborated correctly"
  trivial

def andOrPolicyValue : PolicyValueEval := fun _ => do
  return (0.0, #[
    ("constructor", #[], 1.0),
    ("exact hP", #[], 1.0),
    ("exact hQ", #[], 1.0)
  ])

def transPolicyValue : PolicyValueEval := fun _ => do
  return (0.0, #[
    ("trans b", #[], 1.0),
    ("exact h1", #[], 1.0),
    ("exact h2", #[], 1.0)
  ])

def existsPolicyValue : PolicyValueEval := fun _ => do
  return (0.0, #[
    ("constructor", #[], 1.0),
    ("exact 0", #[], 1.0),
    ("rfl", #[], 1.0)
  ])

def selfLoopPolicyValue : PolicyValueEval := fun _ => do
  return (0.0, #[
    ("skip", #[], 1.0),
    ("trivial", #[], 1.0)
  ])

def noSolutionPolicyValue : PolicyValueEval := fun _ => do
  return (0.0, #[
    ("skip", #[], 1.0)
  ])

def hasLocalDeclNamed (goals : List MVarId) (name : Name) : MetaM Bool := do
  let some goal := goals.head? | return false
  goal.withContext do
    for localDecl in ← getLCtx do
      if localDecl.userName == name then
        return true
    return false

def ancestorLoopPolicyValue : PolicyValueEval := fun goals => do
  if ← hasLocalDeclNamed goals `h then
    return (0.0, #[
      ("clear h", #[], 1.0),
      ("exact True.intro", #[], 1.0)
    ])
  else
    return (0.0, #[
      ("have h : True := by trivial", #[], 1.0),
      ("have h : True := by trivial", #[], 1.0)
    ])

def deferredHavePolicyValue (unfocusedVisits : IO.Ref Nat) : PolicyValueEval := fun goals => do
  if ← hasLocalDeclNamed goals `h then
    return (0.0, #[("exact h", #[], 1.0)])
  let visits ← unfocusedVisits.get
  unfocusedVisits.set (visits + 1)
  if visits == 0 then
    return (0.0, #[("have h : P := ?_", #[], 1.0)])
  else
    return (0.0, #[("exact hP", #[], 1.0)])

def testConfig (maxGoals maxSteps : Nat) : ReapConfig := {
  limits := { total := { maxGoals, maxSteps } }
}

def runMCTSForTest (evalPolicyValue : PolicyValueEval) (config : ReapConfig) :
    TacticM (Option Nat × Array (Node MCTS.NodeData (MCTS.EdgeData × Nat))) := unsafe do
  let ctx ← mkProofCheckContext
  MCTS.monteCarloTreeSearch ctx evalPolicyValue config (← MCTS.NodeData.fromState) none

def childTacticStrings (node : Node MCTS.NodeData (MCTS.EdgeData × Nat)) : Array String :=
  node.children.map fun (edge, _) => edge.tacticStr

def guardProofScriptEquals
    (nodes : Array (Node MCTS.NodeData (MCTS.EdgeData × Nat))) (nodeIdx : Nat)
    (expected : String) : TacticM Unit := do
  match MCTS.proofScriptForSolvedNode nodes nodeIdx with
  | .ok actual =>
      unless actual == expected do
        throwError "unexpected proof script:\nexpected:\n{expected}\nactual:\n{actual}"
  | .error err => throwError err

def guardProofScriptChecks (limits : ReapStepLimitsConfig) (ctx : ProofCheckContext)
    (script : String) : TacticM Unit := do
  match ← checkProofScript limits ctx script with
  | .ok _ => pure ()
  | .error err => throwError "generated proof script failed checking: {(toJson err).compress}"

example (P Q : Prop) (hP : P) (hQ : Q) : P ∧ Q := by
  constructor
  run_tac do
    let kind ← MCTS.childKindAfterTactic
    unless kind == .andNode do
      throwError "expected constructor on conjunction to create an AND node"
  · exact hP
  · exact hQ

example : ∃ n : Nat, n = n := by
  constructor
  run_tac do
    let kind ← MCTS.childKindAfterTactic
    unless kind == .orNode do
      throwError "expected constructor on existential with metavariable goals to stay an OR node"
  · rfl
  · exact 0

example : True := by
  run_tac do
    let (_, nodes) ← runMCTSForTest selfLoopPolicyValue (testConfig 8 8)
    let some root := nodes[0]? | unreachable!
    let tactics := childTacticStrings root
    if tactics.contains "skip" then
      throwError "expected ancestor self-loop tactic to be dropped"
    unless tactics.contains "trivial" do
      throwError "expected non-loop solving tactic to remain"

example : True := by
  run_tac do
    let (_, nodes) ← runMCTSForTest ancestorLoopPolicyValue (testConfig 8 8)
    let some root := nodes[0]? | unreachable!
    unless root.children.size == 1 do
      throwError "expected duplicate non-loop child states to merge"
    let some (rootEdge, childIdx) := root.children[0]? | unreachable!
    unless rootEdge.tacticStr == "have h : True := by trivial" do
      throwError "unexpected root tactic after duplicate merge: {rootEdge.tacticStr}"
    unless rootEdge.probability > 1.9 do
      throwError "expected duplicate child prior mass to be merged"
    let some child := nodes[childIdx]? | unreachable!
    let tactics := childTacticStrings child
    if tactics.contains "clear h" then
      throwError "expected depth ancestor-loop tactic to be dropped"
    unless tactics.contains "exact True.intro" do
      throwError "expected non-loop child solving tactic to remain"

example (P Q : Prop) (hP : P) (hQ : Q) : P ∧ Q := by
  run_tac do
    let saved ← saveState
    let ctx ← mkProofCheckContext
    let (some nodeIdx, nodes) ← runMCTSForTest andOrPolicyValue (testConfig 32 32)
      | throwError "expected MCTS to solve conjunction"
    saved.restore
    let expected := "constructor\n· exact hP\n· exact hQ"
    guardProofScriptEquals nodes nodeIdx expected
    guardProofScriptChecks (testConfig 32 32).limits.step ctx expected
  constructor
  · exact hP
  · exact hQ

example (P : Prop) (hP : P) : P := by
  run_tac do
    let saved ← saveState
    let ctx ← mkProofCheckContext
    let unfocusedVisits ← IO.mkRef 0
    let (some nodeIdx, nodes) ← runMCTSForTest (deferredHavePolicyValue unfocusedVisits)
        (testConfig 32 32)
      | throwError "expected MCTS to solve deferred have proof"
    saved.restore
    let expected := "have h : P := ?_\n· exact h\n· exact hP"
    guardProofScriptEquals nodes nodeIdx expected
    guardProofScriptChecks (testConfig 32 32).limits.step ctx expected
  exact hP

example (P Q : Prop) (hP : P) (hQ : Q) : P ∧ Q := by
  run_tac do
    let saved ← saveState
    let progressRef ← IO.mkRef #[]
    let report : ProgressReporter := fun progress => do
      progressRef.modify fun progressValues => progressValues.push progress
    let result ← runMCTS andOrPolicyValue (testConfig 32 32) (some report)
    saved.restore
    unless result.solution?.isSome do
      throwError "expected MCTS to solve conjunction"
    let progressValues ← progressRef.get
    if progressValues.isEmpty then
      throwError "expected MCTS progress reporter to be called"
    unless progressValues.any (fun progress => progress.visitedNodes > 1) do
      throwError "expected MCTS progress to move past the root node"
    unless progressValues.any (fun progress => progress.done && progress.solved) do
      throwError "expected MCTS progress to report solved completion"
  constructor
  · exact hP
  · exact hQ

example (a b c : Nat) (h1 : a = b) (h2 : b = c) : a = c := by
  run_tac do
    let saved ← saveState
    let ctx ← mkProofCheckContext
    let (some nodeIdx, nodes) ← runMCTSForTest transPolicyValue (testConfig 32 32)
      | throwError "expected MCTS to solve transitivity"
    saved.restore
    let expected := "trans b\n· exact h1\n· exact h2"
    guardProofScriptEquals nodes nodeIdx expected
    guardProofScriptChecks (testConfig 32 32).limits.step ctx expected
  trans b
  · exact h1
  · exact h2

example : True := by
  run_tac do
    let saved ← saveState
    let (solution?, nodes) ← runMCTSForTest noSolutionPolicyValue (testConfig 8 8)
    saved.restore
    if solution?.isSome then
      throwError "expected no solution"
    match MCTS.proofScriptForSolvedNode nodes 0 with
    | .ok script => throwError "expected proof script generation to fail, got:\n{script}"
    | .error _ => pure ()
  trivial

example (a b c : Nat) (h1 : a = b) (h2 : b = c) : a = c := by
  run_tac reapMCTS transPolicyValue (testConfig 32 32)

example (P Q : Prop) (hP : P) (hQ : Q) : P ∧ Q := by
  run_tac reapMCTS andOrPolicyValue (testConfig 32 32)

example : ∃ n : Nat, n = n := by
  run_tac reapMCTS existsPolicyValue (testConfig 32 32)
