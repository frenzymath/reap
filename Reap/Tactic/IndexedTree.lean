module

public meta import Batteries.Data.Array
public meta import Lean

namespace Reap.TreeSearch

public section

/- σ : type of data associated with each node
   ε : type of data associated with each edge
-/
structure Node (σ ε : Type) where
  data : σ
  children : Array ε := #[]

/- Helper functions for working with an array of objects in StateT. -/
variable {σ : Type} {m : Type → Type} [Monad m]

/-- Push a new element onto the state array, returning its index. -/
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

end

end Reap.TreeSearch
