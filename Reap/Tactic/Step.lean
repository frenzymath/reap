module
public meta import Lean
public meta import Reap.Tactic.WallClock

open Lean Meta Elab Tactic
open Reap.WallClock

public meta section

namespace Reap.TreeSearch

def withHeartbeats {m : Type _ → Type _} {α : Type _} [Monad m] [MonadWithReaderOf Core.Context m] (heartbeats : Nat) : m α → m α :=
  withReader (fun s => { s with maxHeartbeats := heartbeats })

partial def collectAuxDeclNames (lctx : LocalContext) (e : Expr) (names : Array Name := #[]) : Array Name :=
  match e with
  | .fvar fvarId =>
    match lctx.auxDeclToFullName.get? fvarId with
    | some name => if names.contains name then names else names.push name
    | none => names
  | .app f a => collectAuxDeclNames lctx a (collectAuxDeclNames lctx f names)
  | .lam _ d b _ | .forallE _ d b _ =>
    collectAuxDeclNames lctx b (collectAuxDeclNames lctx d names)
  | .letE _ t v b _ =>
    collectAuxDeclNames lctx b (collectAuxDeclNames lctx v (collectAuxDeclNames lctx t names))
  | .mdata _ b | .proj _ _ b => collectAuxDeclNames lctx b names
  | _ => names

def replaceAuxDeclFVars (lctx : LocalContext) (auxName : Name) (declName : Name) (levelParams : List Name) (sectionVars : Array Expr) (e : Expr) : Expr :=
  e.replace fun
    | .fvar fvarId =>
      match lctx.auxDeclToFullName.get? fvarId with
      | some name => if name == auxName then some (mkAppN (mkConst declName (levelParams.map mkLevelParam)) sectionVars) else none
      | none => none
    | _ => none

def checkPreDefinitions (preDefs : Array PreDefinition) : TermElabM Bool := withoutModifyingState do
  try
    withOptions (Elab.async.set · false) do
      withoutModifyingEnv do
        addPreDefinitions (← getLCtx, ← getLocalInstances) preDefs
    return !(← getThe Core.State).messages.hasErrors
  catch _ =>
    return false

def getNonAuxFVars : MetaM (Array Expr) := do
  let lctx ← getLCtx
  return lctx.getFVars.filter fun x =>
    !(lctx.find? x.fvarId! |>.any (·.isAuxDecl))

def getNumSectionVars (goals : List MVarId) : TacticM Nat := do
  let some goal := goals.head? | return 0
  goal.withContext do
    let sectionFVarIds := (← readThe Term.Context).sectionFVars.valuesArray.filterMap fun
      | .fvar fvarId => some fvarId
      | _ => none
    let xs ← getNonAuxFVars
    let mut numSectionVars := 0
    for x in xs do
      if sectionFVarIds.contains x.fvarId! then
        numSectionVars := numSectionVars + 1
      else
        break
    return numSectionVars

def mkPreDefinition (numSectionVars : Nat) (goal : MVarId) : TacticM (Option PreDefinition) := do
  goal.withContext do
    unless (← goal.isAssigned) do
      return none
    let lctx ← getLCtx
    let xs ← getNonAuxFVars
    if numSectionVars > xs.size then
      return none
    let sectionVars := xs.extract 0 numSectionVars
    let type ← instantiateMVars (← goal.getType)
    let value ← instantiateMVars (mkMVar goal)
    if type.hasExprMVar || value.hasExprMVar || value.hasSorry then
      return none
    let declName ← mkFreshUserName `_step_check
    let (_, levelParamState) := StateT.run (m := Id) (s := { : CollectLevelParams.State}) do
      modify (·.collect type)
      modify (·.collect value)
    let levelParams := levelParamState.params.toList
    let auxNames := collectAuxDeclNames lctx value
    let some value := (
      match auxNames with
      | #[] => some value
      | #[auxName] => some <| replaceAuxDeclFVars lctx auxName declName levelParams sectionVars value
      | _ => none
    ) | return none
    let type ← mkForallFVars xs type
    let value ← mkLambdaFVars xs value
    return some {
      ref := .missing
      kind := .theorem
      levelParams
      modifiers := {}
      declName
      binders := .missing
      type
      value
      numSectionVars
      termination := .none
    }

def checkProof (numSectionVars : Nat) (originalGoals : List MVarId) : TacticM Bool := do
  for g in originalGoals do
    if ← g.isAssigned then
      let e ← instantiateMVars (mkMVar g)
      if e.hasSorry || e.hasExprMVar then
        return False

  let mut preDefs := #[]
  for goal in originalGoals do
    let some preDef ← mkPreDefinition numSectionVars goal | return false
    preDefs := preDefs.push preDef
  checkPreDefinitions preDefs

def evalTacticStr (numSectionVars : Nat) (originalGoals : List MVarId) (str : String) (heartbeats : Nat) : TacticM (Option Tactic.SavedState) := do
  withCumulativeWallClockTime "reap.wall.tactic_eval" do
    let .ok stx := Parser.runParserCategory (← getEnv) `tactic str | return none
    try
      let (success, messages) ← withCapturedMessages do
        tryCatchRuntimeEx (handler := fun _ => return false) do
          withHeartbeats heartbeats do
            evalTactic stx
            Term.synthesizeSyntheticMVarsNoPostponing
          return true
      if success then
        pruneSolvedGoals
        if hasErrorMessages messages then
          return none
        if (← getGoals).isEmpty then
          if !(← checkProof numSectionVars originalGoals) then
            return none
      else
        return none
    catch _ =>
      return none
    return ← Tactic.saveState

end Reap.TreeSearch
