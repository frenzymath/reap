import Reap.Options
import Reap.PremiseSelection.API

open Lean.LibrarySuggestions

open Lean

def reapSelector : Selector := ppSelector
  fun ppStr _ => do
  let rs ← PremiseSelectionClient.getPremises ppStr
  return rs.map fun x => {name := x.formal_name.toName, score := 1.0}
