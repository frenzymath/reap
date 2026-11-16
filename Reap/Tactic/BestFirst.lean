module
public meta import Batteries
public meta import Lean
public meta import Reap.Options
public meta import Reap.Tactic.State
public meta import Reap.Tactic.Step
public meta import Reap.Tactic.IndexedTree
public meta import Reap.Tactic.TreeSearch
open Lean Meta Elab Tactic

public meta section

/-!
AO*-style best-first search over the same AND/OR tree that MCTS builds.

Every new OR node is evaluated once with the policy/value model when it is
created. The value is stored in `NodeData` (`valueSum`, `numVisit = 1`) and the
proposed tactics are kept until the node is expanded.

Scores use the MCTS conventions (higher is better):
* a solved node scores `0`;
* an unexpanded OR node scores its value-model output;
* an expanded OR node scores the best `child - edgeStepCost edge`, or `-∞` when
  it has no children;
* an AND node scores the worst `child - edgeStepCost edge` over its unsolved
  focus children, as in `MCTS.backpropValueTowardsMin`.

Each step follows the best partial solution from the root (best child at OR
nodes, worst unsolved child at AND nodes) down to an unexpanded OR node and
expands it with `MCTS.expandNode`.
-/

namespace Reap.TreeSearch
namespace BestFirst
open MCTS

/-- Search bookkeeping kept outside `NodeData`, so MCTS data stays unchanged. -/
structure SearchState where
  /-- Policy output of evaluated OR nodes that have not been expanded yet. -/
  pending : Std.HashMap Nat PolicyTactics := {}
  /-- OR nodes whose tactics have been applied. -/
  expanded : Std.HashSet Nat := {}

/-- Call the policy/value model on an unsolved OR node and record the result. -/
def evaluateNode (evalPolicyValue : PolicyValueEval) (st : SearchState) (nodeIdx : Nat) :
    SearchM SearchState := do
  let node ← getNode nodeIdx
  if node.data.toPlay == .andNode || node.data.isSolved then
    return st
  node.data.state.restore
  let goals ← getUnsolvedGoals
  if goals.isEmpty then
    return st
  let (value, tactics) ← evalPolicyValue goals
  modifyAtT nodeIdx fun node => {
    node with data := { node.data with valueSum := value, numVisit := 1, numEvaluations := 1 }
  }
  return { st with pending := st.pending.insert nodeIdx tactics }

def edgeScore (scores : Array Float) (edge : EdgeData) (childIdx : Nat) : Float :=
  scores.getD childIdx (-Float.inf) - edgeStepCost edge

/-- AO* scores of all nodes. Children always have larger indices than their
parent, so a single pass from the last node to the root suffices. -/
def computeScores (nodes : Array (Node NodeData (EdgeData × Nat))) (st : SearchState) :
    Array Float := Id.run do
  let mut scores := Array.replicate nodes.size (-Float.inf)
  for (node, i) in nodes.zipIdx.reverse do
    let score :=
      if node.data.isSolved then
        0.0
      else
        match node.data.toPlay with
        | .orNode =>
            if st.expanded.contains i then
              node.children.foldl (init := -Float.inf) fun best (e, c) => max best (edgeScore scores e c)
            else
              node.data.value
        | .andNode =>
            if node.children.isEmpty then
              -Float.inf
            else
              node.children.foldl (init := 0.0) fun worst (e, c) => min worst (edgeScore scores e c)
    scores := scores.set! i score
  return scores

/-- Among unsolved children, the one whose score is preferred by `better`. -/
def pickChild (nodes : Array (Node NodeData (EdgeData × Nat))) (scores : Array Float)
    (better : Float → Float → Bool) (node : Node NodeData (EdgeData × Nat)) : Option Nat := Id.run do
  let mut best : Option (Nat × Float) := none
  for (e, c) in node.children do
    unless childIsSolved nodes c do
      let s := edgeScore scores e c
      match best with
      | none => best := some (c, s)
      | some (_, b) => if better s b then best := some (c, s)
  return best.map (·.1)

/-- Path from the root along the current best partial solution, ending at the
first unexpanded OR node (or wherever no unsolved child is left). -/
def selectPath (nodes : Array (Node NodeData (EdgeData × Nat))) (st : SearchState)
    (scores : Array Float) : Array Nat := Id.run do
  let mut path := #[0]
  let mut idx := 0
  for _ in [0:nodes.size] do
    let some node := nodes[idx]? | break
    if node.data.toPlay == .orNode && !st.expanded.contains idx then
      break
    let better : Float → Float → Bool := match node.data.toPlay with
      | .orNode => (· > ·)
      | .andNode => (· < ·)
    let some next := pickChild nodes scores better node | break
    path := path.push next
    idx := next
  return path

def searchLoop (ctx : ProofCheckContext) (evalPolicyValue : PolicyValueEval)
    (logConfig : ReapLogConfig) (config : ReapConfig)
    (progress? : Option ProgressReporter) : SearchM (Option Nat × SearchState) := do
    let maxNodes := config.limits.total.maxNodes
    let maxSteps := config.limits.total.maxSteps
    let mut st ← evaluateNode evalPolicyValue {} 0
    let mut step := 0
    while (← get).size <= maxNodes && step < maxSteps && !(← getNode 0).data.isSolved do
      let nodes ← get
      let scores := computeScores nodes st
      if scores.getD 0 (-Float.inf) == -Float.inf then
        break
      let path := selectPath nodes st scores
      let leafIdx := path.back?.getD 0
      let leaf ← getNode leafIdx
      unless leaf.data.toPlay == .orNode && !st.expanded.contains leafIdx do
        throwError "best-first search could not find a frontier node (reached node {leafIdx})"
      let goalType ← currentGoalType leaf.data
      let ancestorKeys := path.foldl (init := ({} : Std.HashSet StateKey)) fun keys i =>
        match nodes[i]? with
        | some node => keys.insert node.data.key
        | none => keys
      let tactics := st.pending.getD leafIdx #[]
      st := { st with pending := st.pending.erase leafIdx, expanded := st.expanded.insert leafIdx }
      let created ← expandNode ctx logConfig config ancestorKeys leafIdx leaf.data tactics
      for childIdx in created do
        st ← evaluateNode evalPolicyValue st childIdx
      for i in path.reverse do
        refreshNodeSolved i
      reportProgress? progress? step maxNodes maxSteps goalType false false "running"
      step := step + 1
    if (← getNode 0).data.isSolved then
      reportProgress? progress? step maxNodes maxSteps "no goals" true true "solved"
      return (some 0, st)
    reportProgress? progress? step maxNodes maxSteps "search exhausted" true false "exhausted"
    return (none, st)

def bestFirstSearch (ctx : ProofCheckContext) (evalPolicyValue : PolicyValueEval)
    (logConfig : ReapLogConfig) (config : ReapConfig) (start : NodeData)
    (progress? : Option ProgressReporter) :
    TacticM (Option Nat × Array (Node NodeData (EdgeData × Nat)) × SearchState) := do
  let ((k, st), nodes) ←
    (searchLoop ctx evalPolicyValue logConfig config progress?).run #[ { data := start } ]
  return (k, nodes, st)

def ppNode (scores : Array Float) (nodeIdx : Nat) (node : Node NodeData (EdgeData × Nat)) :
    TacticM Json := do
  let children := node.children.map fun (e, i) => json%{ edge: $e, childIndex: $i }
  return json%{
    data: $(← ppNodeData node.data),
    score: $(scores.getD nodeIdx (-Float.inf)),
    children: $children
  }

end BestFirst

open MCTS in
def runBestFirst (evalPolicyValue : PolicyValueEval) (logConfig : ReapLogConfig) (config : ReapConfig)
    (progress? : Option ProgressReporter) : TacticM MCTSResult := do
  let ctx ← mkProofCheckContext
  let (k, nodes, st) ←
    BestFirst.bestFirstSearch ctx evalPolicyValue logConfig config (← NodeData.fromState) progress?
  let scores := BestFirst.computeScores nodes st
  let ppNodes ← nodes.zipIdx.mapM fun (node, i) => BestFirst.ppNode scores i node
  let info := json%{
    solution : $k,
    nodes : $ppNodes
  }
  writeRawTree logConfig.rawTree info
  return {
    ctx := ctx
    solution? := k
    nodes := nodes
    info := info
  }

/-- Run the search selected by `config.strategy`. -/
def runSearch (evalPolicyValue : PolicyValueEval) (logConfig : ReapLogConfig) (config : ReapConfig)
    (progress? : Option ProgressReporter) : TacticM MCTSResult :=
  match config.strategy with
  | .mcts => runMCTS evalPolicyValue logConfig config progress?
  | .bestFirst => runBestFirst evalPolicyValue logConfig config progress?

open MCTS in
def reapBestFirst (evalPolicyValue : PolicyValueEval) (logConfig : ReapLogConfig) (config : ReapConfig) :
    TacticM Unit := do
  let result ← runBestFirst evalPolicyValue logConfig config none
  if result.solution?.isSome then
    let some root := result.nodes[0]? | throwError "best-first search result has no root node"
    root.data.state.restore
    replaySolvedNode logConfig config.limits.step result.ctx result.nodes 0
    match ← checkProof result.ctx with
    | .ok _ => return ()
    | .error err => throwError "best-first final proof check failed after replay: {(toJson err).compress}"

/-- Run the search selected by `config.strategy` and close the goal with the proof found. -/
def reapSearch (evalPolicyValue : PolicyValueEval) (logConfig : ReapLogConfig) (config : ReapConfig) :
    TacticM Unit :=
  match config.strategy with
  | .mcts => reapMCTS evalPolicyValue logConfig config
  | .bestFirst => reapBestFirst evalPolicyValue logConfig config

end Reap.TreeSearch
