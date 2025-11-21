module
public meta import Aesop
public meta import Reap.Tactic.Generator
public meta import Reap.Tactic.Ruleset

public meta section

@[aesop 100% (rule_sets := [reap])]
def reapTacGen : Aesop.TacGen := TacticGenerator.generateTactics

elab "reap!!" : tactic => do
  let opts ← Lean.getOptions
  let maxGoals := reap.max_goals.get opts
  let maxGoalsStx := Lean.Syntax.mkNumLit (toString maxGoals)
  Lean.Elab.Tactic.evalTactic (← `(tactic| aesop? (config := {
    enableSimp := false,
    enableUnfold := false,
    maxGoals := $maxGoalsStx}) (rule_sets := [reap])))
