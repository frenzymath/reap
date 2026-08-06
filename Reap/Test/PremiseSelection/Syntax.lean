import Reap.PremiseSelection.Syntax

open Lean Elab Tactic
open Lean.LibrarySuggestions

theorem bridgePremiseOne (n : Nat) : n = n := rfl

theorem bridgePremiseTwo : True := True.intro

def fakeBridgeSelector : Selector := fun _ config => do
  let suggestions : Array Suggestion := #[
    { name := ``bridgePremiseOne, score := 1.0 },
    { name := ``bridgePremiseTwo, score := 0.9 },
    { name := ``bridgePremiseOne, score := 0.5 }
  ]
  let suggestions ← suggestions.filterM fun s => config.filter s.name
  return suggestions.take config.maxSuggestions

set_library_suggestions fakeBridgeSelector

elab "guardSelectPremisesForGoals" : tactic => do
  let premises ← selectPremisesForGoals (← getGoals) 2
  match premises[0]?, premises[1]? with
  | some first, some second =>
      unless first.formal_name == "bridgePremiseOne" do
        throwError "unexpected first premise: {first.formal_name}"
      unless second.formal_name == "bridgePremiseTwo" do
        throwError "unexpected second premise: {second.formal_name}"
      if first.formal_statement.isEmpty || second.formal_statement.isEmpty then
        throwError "expected non-empty formal statements"
  | _, _ =>
      throwError "expected two premises, got {premises.size}"

example (n : Nat) : n = n := by
  guardSelectPremisesForGoals
  rfl
