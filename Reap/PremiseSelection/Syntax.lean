module
public meta import Lean.LibrarySuggestions.Basic
public meta import Reap.Options
public meta import Reap.PremiseSelection.API
public meta section

open Lean
open Lean.LibrarySuggestions

def reapSelector : Selector := ppSelector fun ppStr config => do
  let rs ← PremiseSelectionClient.getPremises ppStr config.maxSuggestions
  let suggestions := rs.map fun x => {
    name := x.formal_name.toName
    score := 1.0
  }
  suggestions.filterM fun s => config.filter s.name

def suggestionToPremiseSelectionResult? (suggestion : Suggestion) :
    MetaM (Option PremiseSelectionResult) := do
  try
    let decl ← getConstInfo suggestion.name
    let statement ← Meta.ppExpr decl.type
    return some {
      formal_name := toString suggestion.name
      formal_statement := toString statement
    }
  catch _ =>
    return none

def selectPremisesForGoals (mvarIds : List MVarId) (maxSuggestions : Nat) :
    MetaM (Array PremiseSelectionResult) := do
  let mut seen : NameSet := {}
  let mut premises := #[]
  for mvarId in mvarIds do
    if premises.size >= maxSuggestions then
      break
    let suggestions ← Lean.LibrarySuggestions.select mvarId { maxSuggestions := maxSuggestions }
    for suggestion in suggestions do
      if premises.size >= maxSuggestions then
        break
      unless seen.contains suggestion.name do
        match ← suggestionToPremiseSelectionResult? suggestion with
        | some premise =>
            seen := seen.insert suggestion.name
            premises := premises.push premise
        | none =>
            pure ()
  return premises
