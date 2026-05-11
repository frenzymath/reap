import Reap.Tactic.Step

open Lean Meta Elab Tactic Reap.TreeSearch

elab "guardEvalAccepts " s:str : tactic => do
  let originalGoals ← getUnsolvedGoals
  let numSectionVars ← getNumSectionVars originalGoals
  let some st ← evalTacticStr numSectionVars originalGoals s.getString 200000
    | throwError "expected tactic to be accepted"
  st.restore

elab "guardEvalRejects " s:str : tactic => do
  withoutModifyingState do
    let originalGoals ← getUnsolvedGoals
    let numSectionVars ← getNumSectionVars originalGoals
    let result ← evalTacticStr numSectionVars originalGoals s.getString 200000
    match result with
    | none => pure ()
    | some _ => throwError "expected tactic to be rejected"

theorem evalTacticStr_accepts_trivial : True := by
  guardEvalAccepts "trivial"

theorem evalTacticStr_accepts_recursive (n : Nat) : True := by
  guardEvalAccepts "cases n with | zero => trivial | succ n => exact evalTacticStr_accepts_recursive n"

section

variable (α : Type) (x : α)

theorem evalTacticStr_accepts_recursive_with_section_var (n : Nat) : x = x := by
  guardEvalAccepts "cases n with | zero => rfl | succ n => exact evalTacticStr_accepts_recursive_with_section_var n"

end

theorem evalTacticStr_rejects_self_reference : False := by
  guardEvalRejects "exact evalTacticStr_rejects_self_reference"
  sorry
