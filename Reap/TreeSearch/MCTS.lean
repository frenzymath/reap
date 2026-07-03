module
public meta import Batteries.Data.Array
public meta import Reap.TreeSearch.Basic
public meta import Lean

namespace TreeSearch

public meta section
/- Helper functions for working with an array of objects in StateT -/
variable {σ : Type} {m : Type → Type} [Monad m]

/-- Push a new element onto the state array, returning its index -/
def pushT (x : σ) : StateT (Array σ) m Nat :=
  .modifyGet fun a => (a.size, a.push x)

def getAtT (i : Nat) (d : σ) : StateT (Array σ) m σ := do
  return (← get)[i]?.getD d

def getsAtT {τ : Type} (i : Nat) (f : σ → τ) (d : τ) : StateT (Array σ) m τ := do
  return (← get)[i]?.elim d f

def setAtT (i : Nat) (x : σ) : StateT (Array σ) m Unit :=
  modify fun a => a.set! i x

def modifyAtT (i : Nat) (f : σ → σ) : StateT (Array σ) m Unit :=
  modify fun a => a.modify i f

end

public meta section
abbrev IndexedTreeT σ ε m := StateT (Array (Node σ (ε × Nat))) m

variable {σ ε : Type}
variable {m : Type → Type} [Monad m]

local notation "SearchM" => IndexedTreeT σ ε m

def resolve (node : Node σ (ε × Nat)) : SearchM (Node σ (ε × σ)) := do
  let data := node.data
  let children ← node.children.mapM fun (e, i) => do pure (e, ← getsAtT i Node.data data)
  return { data, children }

def pushChildT (parentIdx : Nat) (edge : ε) (childData : σ) : SearchM Nat := do
  let childIdx ← pushT { data := childData }
  let nodes ← get
  if let some parent := nodes[parentIdx]? then
    setAtT parentIdx { parent with children := parent.children.push (edge, childIdx) }
  return childIdx

def pushChildrenT (parentIdx : Nat) (children : Array (ε × σ)) : SearchM (Array Nat) := do
  let mut childIndices := #[]
  for (edge, childData) in children do
    childIndices := childIndices.push (← pushChildT parentIdx edge childData)
  return childIndices

unsafe def mctsStep
    (visitNode : Nat → Node σ (ε × σ) → SearchM Unit)
    (selectChild : Node σ (ε × σ) → SearchM (Option Nat))
    (updateEdge : σ → ε → σ → σ → SearchM ε)
    (updateNode : Node σ (ε × σ) → σ → SearchM σ)
    (i : Nat) : SearchM σ := do
  let nodes ← get
  let x := nodes[i]'lcProof
  let node ← resolve x
  match ← selectChild node with
  | none =>
      visitNode i node
      return nodes[i]'lcProof |>.data
  | some k =>
      let (_, j) := x.children[k]'lcProof
      let data ← mctsStep visitNode selectChild updateEdge updateNode j
      let x ← getAtT i x
      let (e, _) := x.children[k]'lcProof
      let e' ← updateEdge x.data e (← getsAtT j Node.data x.data) data
      let x ← getAtT i x
      let x := { x with children := x.children.set! k (e', j) }
      setAtT i x
      let s' ← updateNode (← resolve x) data
      let x ← getAtT i x
      setAtT i { x with data := s' }
      return data

def MCTS.defaultMaxNodes : Nat := 64
def MCTS.defaultMaxSteps : Nat := 64

unsafe def monteCarloTreeSearch
    (isTerminal : σ → SearchM Bool)
    (visitNode : Nat → Node σ (ε × σ) → SearchM Unit)
    (selectChild : Node σ (ε × σ) → SearchM (Option Nat))
    (updateEdge : σ → ε → σ → σ → SearchM ε)
    (updateNode : Node σ (ε × σ) → σ → SearchM σ)
    (start : σ)
    (maxNodes := MCTS.defaultMaxNodes)
    (maxSteps := MCTS.defaultMaxSteps) :
    m (Option Nat × Array (Node σ (ε × Nat))) :=
  StateT.run (s := #[ { data := start } ]) do
    let mut step := 0
    while (← get).size <= maxNodes && step < maxSteps do
      discard <| mctsStep visitNode selectChild updateEdge updateNode 0
      let result ← (← get).findIdxM? fun x => isTerminal x.data
      if result.isSome then
        return result
      step := step + 1
    return none
end

end TreeSearch
