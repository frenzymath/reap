import Aesop
import Reap.Tactic.Generator
import Reap.Tactic.Ruleset

@[aesop 100% (rule_sets := [reap])]
def reapTacGen : Aesop.TacGen := TacticGenerator.generateTactics

macro "reap!!" : tactic => `(tactic| aesop? (config := {
    enableSimp := false,
    enableUnfold := false,
    maxGoals := 64}) (rule_sets := [reap]))
