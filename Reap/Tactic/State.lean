module

public meta import Lean

open Lean Meta Elab Tactic

public meta section

namespace Reap.TreeSearch

def containsDefEqType (types : Array Expr) (type : Expr) : MetaM Bool := do
  for seen in types do
    if ← isDefEqGuarded seen type then
      return true
  return false

def duplicatePropFVarIds : MetaM (Array FVarId) := do
  let mut seenTypes := #[]
  let mut duplicates := #[]
  for localDecl in (← getLCtx) do
    unless localDecl.isImplementationDetail || localDecl.hasValue do
      let type ← instantiateMVars localDecl.type
      if ← isProp type then
        if ← containsDefEqType seenTypes type then
          duplicates := duplicates.push localDecl.fvarId
        else
          seenTypes := seenTypes.push type
  return duplicates

def dedupPropContext (goal : MVarId) : MetaM MVarId :=
  goal.withContext do
    goal.tryClearMany (← duplicatePropFVarIds)

def simplifyState : TacticM Unit := do
  let goals ← getGoals
  setGoals (← goals.mapM fun goal => liftM (dedupPropContext goal : MetaM MVarId))

abbrev StateKey := String

example : Hashable StateKey := inferInstance

def stateKey : TacticM StateKey := do
  let goals ← getUnsolvedGoals
  let pp ← goals.toArray.mapM fun goal => do
    return toString (← Meta.ppGoal goal)
  return toJson pp |>.compress

end Reap.TreeSearch
