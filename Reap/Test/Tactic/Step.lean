import Reap.Tactic.Step

open Lean Meta Elab Tactic Reap.TreeSearch

partial def formatSyntaxTree (stx : Syntax) (indent : Nat := 0) : String :=
  let pad := String.ofList (List.replicate indent ' ')
  match stx with
  | .missing => s!"{pad}<missing>"
  | .atom _ val => s!"{pad}atom {val}"
  | .ident _ _ val _ => s!"{pad}ident {val}"
  | .node _ kind args =>
      let children := args.toList.map (fun arg => formatSyntaxTree arg (indent + 2))
      match children with
      | [] => s!"{pad}node {kind}"
      | _ => s!"{pad}node {kind}\n{String.intercalate "\n" children}"

elab "print_syntax_tree " s:str : tactic => do
  match ← parseTacticStr s.getString with
  | .ok stx => logInfo (formatSyntaxTree stx)
  | .error err => throwError "failed to parse tactic: {toString err}"

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

elab "guardRunTacticSyntaxTimesOut " s:str : tactic => do
  withoutModifyingState do
    match ← parseTacticStr s.getString with
    | .error err => throwError "failed to parse tactic: {toString err}"
    | .ok stx =>
        match ← runTacticSyntax stx 1000000000000 100 with
        | .error .tacticTimeout => pure ()
        | .error err => throwError "expected tactic timeout, got: {toString err}"
        | .ok _ => throwError "expected tactic timeout, got success"

elab "guardRunTacticSyntaxAccepts " s:str : tactic => do
  match ← parseTacticStr s.getString with
  | .error err => throwError "failed to parse tactic: {toString err}"
  | .ok stx =>
      match ← runTacticSyntax stx 200000 5000 with
      | .ok _ => pure ()
      | .error err => throwError "expected tactic success, got: {toString err}"

elab "guardRunTacticSyntaxRejectsNonTimeout " s:str : tactic => do
  withoutModifyingState do
    match ← parseTacticStr s.getString with
    | .error err => throwError "failed to parse tactic: {toString err}"
    | .ok stx =>
        match ← runTacticSyntax stx 200000 5000 with
        | .error .tacticTimeout => throwError "expected non-timeout tactic error"
        | .error _ => pure ()
        | .ok _ => throwError "expected tactic error, got success"

theorem evalTacticStr_accepts_trivial : True := by
  guardEvalRejects "show True from grind?"
  guardEvalRejects "apply?"
  guardEvalRejects "sorry"
  guardEvalRejects "hint"
  guardEvalRejects "repeat' trivial"
  guardEvalAccepts "trivial"

theorem evalTacticStr_rejects_placeholder_closed_goal : True := by
  guardEvalRejects "cases (_ : False)"
  trivial

theorem print_syntax_tree : True := by
  print_syntax_tree "have theorem? := ?_"
  print_syntax_tree "apply?"
  trivial

theorem runTacticSyntax_times_out_repeat_have : True := by
  guardRunTacticSyntaxTimesOut "repeat' have h : True := by trivial"
  trivial

theorem runTacticSyntax_accepts_with_timeout : True := by
  guardRunTacticSyntaxAccepts "trivial"

theorem runTacticSyntax_rejects_without_timeout : True := by
  guardRunTacticSyntaxRejectsNonTimeout "exact (0 : Nat)"
  trivial

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
