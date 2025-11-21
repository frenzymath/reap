module
public meta import Reap.Options
public meta import Reap.PremiseSelection.API
public meta section
open Lean.LibrarySuggestions

open Lean

def reapSelector : Selector := ppSelector
  fun ppStr _ => do
  let rs ← PremiseSelectionClient.getPremises ppStr
  return rs.map fun x => {name := x.formal_name.toName, score := 1.0}
