module
public meta import Lean
public meta import Reap.Tactic.Generator
public meta import Reap.Tactic.WallClock

open Lean Meta Elab Tactic
open Reap.WallClock

public meta section

namespace Reap.TreeSearch

def withHeartbeats {m : Type _ → Type _} {α : Type _}
    [Monad m] [MonadWithReaderOf Core.Context m] [MonadControlT CoreM m]
    (heartbeats : Nat) (x : m α) : m α :=
  withCurrHeartbeats <|
    withReader (fun s => { s with maxHeartbeats := heartbeats }) x

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

structure ProofCheckContext where
  numSectionFVars : Nat
  originalGoals : List MVarId

def mkProofCheckContext : TacticM ProofCheckContext := do
  let originalGoals ← getUnsolvedGoals
  return {
    numSectionFVars := (← getNumSectionVars originalGoals)
    originalGoals := originalGoals
  }

inductive EvalError where
  | parseError (message : String)
  | forbiddenTactic (kind : SyntaxNodeKind)
  | tacticException (message : String)
  | tacticErrorMessages (messages : List SerialMessage)
  | unassignedGoal
  | assignedProofHasMVarOrSorry
  | auxProofHasMVarOrSorry (declName : Name)
  | auxProofKernelCheckFailed (declName : Name) (message : String)
  | finalProofCheckFailed
deriving ToJson

namespace EvalError

def fromException (ex : Exception) : CoreM EvalError := do
  return .tacticException (← ex.toMessageData.toString)

end EvalError

instance : ToString EvalError where
  toString err := (toJson err).compress

abbrev EvalResult α := Except EvalError α

instance : ToJson (EvalResult Unit) where
  toJson
  | .ok _ => json%{ "ok": null }
  | .error e => json% { "error": $e }

def withCatchRuntime {α : Type} (act : TacticM (EvalResult α)) : TacticM (EvalResult α) := do
  try
    tryCatchRuntimeEx (handler := fun ex => do return .error (← EvalError.fromException ex))
      act
  catch ex =>
    return .error (← EvalError.fromException ex)

def mkPreDefinition (numSectionVars : Nat) (goal : MVarId) : TacticM (Option PreDefinition) := do
  goal.withContext do
    let lctx ← getLCtx
    let xs ← getNonAuxFVars
    if numSectionVars > xs.size then
      return none
    let sectionVars := xs.extract 0 numSectionVars
    let type ← instantiateMVars (← goal.getType)
    let value ← instantiateMVars (mkMVar goal)
    if type.hasExprMVar then
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

partial def collectConstNames (e : Expr) (names : Array Name := #[]) : Array Name :=
  match e with
  | .const name _ => if names.contains name then names else names.push name
  | .app f a => collectConstNames a (collectConstNames f names)
  | .lam _ d b _ | .forallE _ d b _ =>
    collectConstNames b (collectConstNames d names)
  | .letE _ t v b _ =>
    collectConstNames b (collectConstNames v (collectConstNames t names))
  | .mdata _ b | .proj _ _ b => collectConstNames b names
  | _ => names

partial def checkCurrentAuxDeclsInExpr (parentDeclName : Name) (e : Expr) (checked : Array Name := #[]) : TacticM (Except EvalError (Array Name)) := do
  let mut checked := checked
  for constName in collectConstNames e do
    if parentDeclName.isPrefixOf constName && constName != parentDeclName && !checked.contains constName then
      checked := checked.push constName
      let info ← getConstInfo constName
      if let some value := info.value? then
        if value.hasSorry || value.hasExprMVar then
          return .error (.auxProofHasMVarOrSorry constName)
        try
          Meta.checkWithKernel value
        catch ex =>
          return .error (.auxProofKernelCheckFailed constName (← ex.toMessageData.toString))
        match ← checkCurrentAuxDeclsInExpr parentDeclName value checked with
        | .ok checked' => checked := checked'
        | .error err => return .error err
  return .ok checked

def checkProof (ctx : ProofCheckContext) : TacticM (EvalResult Unit) := do
  let some parentDeclName ← Term.getDeclName? | return .ok ()
  let mut checked := #[]

  for g in ctx.originalGoals do
    if ← g.isAssigned then
      let e ← instantiateMVars (mkMVar g)
      if e.hasSorry || e.hasExprMVar then
        return .error .assignedProofHasMVarOrSorry
      match ← g.withContext <| checkCurrentAuxDeclsInExpr parentDeclName e checked with
      | .ok checked' => checked := checked'
      | .error err => return .error err
    else
      return .error .unassignedGoal

  let mut preDefs := #[]
  for goal in ctx.originalGoals do
    let some preDef ← mkPreDefinition ctx.numSectionFVars goal | return .error .finalProofCheckFailed
    preDefs := preDefs.push preDef
  if !(← checkPreDefinitions preDefs) then
    return .error .finalProofCheckFailed
  return .ok ()


def isQuestionTacticKind (kind : SyntaxNodeKind) : Bool :=
  kind == `sorry || kind == `admit || kind == `Lean.Parser.Tactic.repeat' ||
    (if let .str _ x := kind then x.endsWith "?" else false)

partial def findQuestionTacticKind (stx : Syntax) : Option SyntaxNodeKind :=
  if isQuestionTacticKind stx.getKind then
    some stx.getKind
  else
    stx.getArgs.findSome? findQuestionTacticKind

def parseTacticStr (str : String) : TacticM (EvalResult Syntax) := do
  match Parser.runParserCategory (← getEnv) `tactic str with
  | .ok stx => return .ok stx
  | .error e => return .error (.parseError e)

def checkTacticSyntax (stx : Syntax) : EvalResult Unit :=
  match findQuestionTacticKind stx with
  | some kind => .error (.forbiddenTactic kind)
  | none => .ok ()

def runTacticSyntax (stx : Syntax) (heartbeats : Nat) : TacticM (EvalResult (List Message)) := do
  let (result, messages) ← withCapturedMessages do
    withCatchRuntime do
      withHeartbeats heartbeats <| evalTactic stx
      Term.synthesizeSyntheticMVarsNoPostponing
      pruneSolvedGoals
      return .ok ()
  return result.map fun _ => messages

def checkMessages (messages : List Message) : TacticM (EvalResult Unit) := do
  if hasErrorMessages messages then
    return .error (.tacticErrorMessages (← messages.filterMapM fun x => if x.severity != .information then x.serialize else return none))
  return .ok ()

def evalTacticStrCore (str : String) (heartbeats : Nat) (checkCtx? : Option ProofCheckContext) : TacticM (EvalResult Unit) := do
  let state := toString <| ← TacticGenerator.Meta.ppProofState (← getGoals)
  withLogWallClockTime "tactic_eval" (fun result => json%{ state: $state, tactic: $str, result: $result }) <| ExceptT.run do
    let stx ← parseTacticStr str
    checkTacticSyntax stx
    let messages ← runTacticSyntax stx heartbeats
    checkMessages messages
    if (← getGoals).isEmpty then
      match checkCtx? with
      | some checkCtx => checkProof checkCtx
      | none => pure ()

def evalTacticStr (ctx : ProofCheckContext) (str : String) (heartbeats : Nat) : TacticM (EvalResult Unit) :=
  evalTacticStrCore str heartbeats (some ctx)

def evalTacticStrNoFinalCheck (_ctx : ProofCheckContext) (str : String) (heartbeats : Nat) : TacticM (EvalResult Unit) :=
  evalTacticStrCore str heartbeats none

end Reap.TreeSearch
