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
  Reap.TreeSearch.reapMCTS TacticGenerator.generateTactics maxGoals

end
