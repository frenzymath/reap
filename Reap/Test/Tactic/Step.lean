import Reap.Tactic.Step

open Lean Meta Elab Tactic Reap.TreeSearch

elab "guardEvalAccepts " s:str : tactic => do
  let ctx ← mkProofCheckContext
  match ← evalTacticStr ctx s.getString 200000 with
  | .ok _ => pure ()
  | .error err => throwError "expected tactic to be accepted, got: {toString err}"

elab "guardEvalRejects " s:str : tactic => do
  withoutModifyingState do
    let ctx ← mkProofCheckContext
    let result ← evalTacticStr ctx s.getString 200000
    if result.isOk then
      throwError "expected tactic to be rejected"

theorem evalTacticStr_accepts_trivial : True := by
  guardEvalRejects "show True from grind?"
  guardEvalRejects "sorry"
  guardEvalRejects "hint"
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
