module
public meta import Reap.Tactic.Generator
public meta import TreeSearch

public meta section

elab "reapBFS" : tactic => do
  let opts ← Lean.getOptions
  let maxGoals := reap.max_goals.get opts
  proofSearchBFS TacticGenerator.generateTactics maxGoals

elab "reapMCTS" : tactic => do
  let opts ← Lean.getOptions
  let maxGoals := reap.max_goals.get opts
  let maxSteps := reap.max_steps.get opts
  Reap.TreeSearch.reapMCTS TacticGenerator.generateTactics TacticGenerator.generateValue maxGoals maxSteps

end
