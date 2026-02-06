module
public meta import Reap.Tactic.Generator
public meta import TreeSearch

public meta section

elab "reapBFS" : tactic => proofSearchBFS TacticGenerator.generateTactics
