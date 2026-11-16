import Reap.Tactic.Syntax

open Lean Meta Elab Tactic
open Reap.TreeSearch

set_option linter.unusedSimpArgs false

namespace Reap.Test.BestFirst

example : True := by
  run_tac do
    let reapStx ←
      match ← parseTacticStr "reap (strategy := .bestFirst) (limits.total.maxNodes := 5)" with
      | .ok stx => pure stx
      | .error err => throwError "failed to parse reap configuration: {toString err}"
    let config ← elabReapConfig reapStx[1]
    unless config.strategy == .bestFirst && config.limits.total.maxNodes == 5 do
      throwError "reap strategy was not elaborated correctly"
    let defaultStx ←
      match ← parseTacticStr "reap" with
      | .ok stx => pure stx
      | .error err => throwError "failed to parse reap: {toString err}"
    let defaultConfig ← elabReapConfig defaultStx[1]
    unless defaultConfig.strategy == .mcts do
      throwError "expected MCTS to be the default strategy"
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

def deferredHavePolicyValue (unfocusedVisits : IO.Ref Nat) : PolicyValueEval := fun goals => do
  if ← hasLocalDeclNamed goals `h then
    return (0.0, #[("exact h", #[], 1.0)])
  let visits ← unfocusedVisits.get
  unfocusedVisits.set (visits + 1)
  if visits == 0 then
    return (0.0, #[("have h : P := ?_", #[], 1.0)])
  else
    return (0.0, #[("exact hP", #[], 1.0)])

/-- The state containing `hGood` is valued higher than the one containing `hBad`;
both can be closed by `trivial`. -/
def valueGuidedPolicyValue (calls : IO.Ref Nat) : PolicyValueEval := fun goals => do
  calls.modify (· + 1)
  if ← hasLocalDeclNamed goals `hGood then
    return (-1.0, #[("trivial", #[], 1.0)])
  if ← hasLocalDeclNamed goals `hBad then
    return (-5.0, #[("trivial", #[], 1.0)])
  return (0.0, #[
    ("have hBad : True := trivial", #[], 1.0),
    ("have hGood : True := trivial", #[], 1.0)
  ])

def testConfig (maxNodes maxSteps : Nat) : ReapConfig := {
  strategy := .bestFirst
  limits := { total := { maxNodes, maxSteps } }
}

def runBestFirstForTest (evalPolicyValue : PolicyValueEval) (config : ReapConfig) :
    TacticM (Option Nat × Array (Node MCTS.NodeData (MCTS.EdgeData × Nat))) := do
  let ctx ← mkProofCheckContext
  let (k, nodes, _) ←
    BestFirst.bestFirstSearch ctx evalPolicyValue {} config (← MCTS.NodeData.fromState) none
  return (k, nodes)

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
  match ← checkProofScript {} limits ctx script with
  | .ok _ => pure ()
  | .error err => throwError "generated proof script failed checking: {(toJson err).compress}"

example (P Q : Prop) (hP : P) (hQ : Q) : P ∧ Q := by
  run_tac do
    let saved ← saveState
    let ctx ← mkProofCheckContext
    let (some nodeIdx, nodes) ← runBestFirstForTest andOrPolicyValue (testConfig 32 32)
      | throwError "expected best-first search to solve conjunction"
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
    let (some nodeIdx, nodes) ← runBestFirstForTest (deferredHavePolicyValue unfocusedVisits)
        (testConfig 32 32)
      | throwError "expected best-first search to solve deferred have proof"
    saved.restore
    let expected := "have h : P := ?_\n· exact h\n· exact hP"
    guardProofScriptEquals nodes nodeIdx expected
    guardProofScriptChecks (testConfig 32 32).limits.step ctx expected
  exact hP

example (a b c : Nat) (h1 : a = b) (h2 : b = c) : a = c := by
  run_tac do
    let saved ← saveState
    let ctx ← mkProofCheckContext
    let (some nodeIdx, nodes) ← runBestFirstForTest transPolicyValue (testConfig 32 32)
      | throwError "expected best-first search to solve transitivity"
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
    let calls ← IO.mkRef 0
    let (some nodeIdx, nodes) ← runBestFirstForTest (valueGuidedPolicyValue calls) (testConfig 32 32)
      | throwError "expected best-first search to solve value-guided goal"
    saved.restore
    guardProofScriptEquals nodes nodeIdx "have hGood : True := trivial\ntrivial"
    let some root := nodes[0]? | unreachable!
    for (edge, childIdx) in root.children do
      let some child := nodes[childIdx]? | unreachable!
      if edge.tacticStr == "have hBad : True := trivial" && !child.children.isEmpty then
        throwError "expected the lower-valued branch to stay unexpanded"
    -- root, hBad and hGood are each evaluated once; the solved leaf is not.
    unless (← calls.get) == 3 do
      throwError "expected 3 policy/value calls, got {← calls.get}"
  trivial

example : True := by
  run_tac do
    let saved ← saveState
    let (solution?, nodes) ← runBestFirstForTest noSolutionPolicyValue (testConfig 8 8)
    saved.restore
    if solution?.isSome then
      throwError "expected no solution"
    match MCTS.proofScriptForSolvedNode nodes 0 with
    | .ok script => throwError "expected proof script generation to fail, got:\n{script}"
    | .error _ => pure ()
  trivial

example (P Q : Prop) (hP : P) (hQ : Q) : P ∧ Q := by
  run_tac do
    let saved ← saveState
    let progressRef ← IO.mkRef #[]
    let report : ProgressReporter := fun progress => do
      progressRef.modify fun progressValues => progressValues.push progress
    let result ← runSearch andOrPolicyValue {} (testConfig 32 32) (some report)
    saved.restore
    unless result.solution?.isSome do
      throwError "expected best-first search to solve conjunction"
    let progressValues ← progressRef.get
    unless progressValues.any (fun progress => progress.visitedNodes > 1) do
      throwError "expected best-first progress to move past the root node"
    unless progressValues.any (fun progress => progress.done && progress.solved) do
      throwError "expected best-first progress to report solved completion"
  constructor
  · exact hP
  · exact hQ

example (a b c : Nat) (h1 : a = b) (h2 : b = c) : a = c := by
  run_tac reapSearch transPolicyValue {} (testConfig 32 32)

example (P Q : Prop) (hP : P) (hQ : Q) : P ∧ Q := by
  run_tac reapSearch andOrPolicyValue {} (testConfig 32 32)

example : ∃ n : Nat, n = n := by
  run_tac reapSearch existsPolicyValue {} (testConfig 32 32)

end Reap.Test.BestFirst
