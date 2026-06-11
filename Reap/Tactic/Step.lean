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
  | tacticTimeout
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

instance [ToJson α] : ToJson (EvalResult α) where
  toJson
  | .ok x => json%{ "ok": $x }
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

partial def checkCurrentAuxDeclsInExpr (parentDeclName : Name) (e : Expr) (checked : Array Name := #[]) : TacticM (EvalResult (Array Name)) := do
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
  match stx with
  | .node _ kind args =>
      if isQuestionTacticKind kind then
        some kind
      else
        args.findSome? findQuestionTacticKind
  | _ => none

partial def collectIdentSyntaxes (stx : Syntax) (idents : Array Syntax := #[]) : Array Syntax :=
  match stx with
  | .ident .. => idents.push stx
  | .node _ _ args => args.foldl (fun idents stx => collectIdentSyntaxes stx idents) idents
  | _ => idents

def syntaxIdentName? : Syntax → Option Name
  | .ident _ _ name _ => some name.eraseMacroScopes
  | _ => none

def isLocalUserName (name : Name) : TacticM Bool := do
  for localDecl in ← getLCtx do
    if localDecl.userName == name then
      return true
  return false

def resolveExplicitConstName? (stx : Syntax) : TacticM (Option Name) := do
  let some rawName := syntaxIdentName? stx | return none
  if ← isLocalUserName rawName then
    return none
  try
    return some (← realizeGlobalConstNoOverloadWithInfo stx)
  catch _ =>
    if (← getEnv).contains rawName then
      return some rawName
    return none

def collectExplicitConstNames (stx : Syntax) : TacticM (Array Name) := do
  let mut names := #[]
  for ident in collectIdentSyntaxes stx do
    if let some name ← resolveExplicitConstName? ident then
      unless names.contains name do
        names := names.push name
  return names

def parseTacticStr (str : String) : TacticM (EvalResult Syntax) := do
  match Parser.runParserCategory (← getEnv) `tactic str with
  | .ok stx => return .ok stx
  | .error e => return .error (.parseError e)

def checkTacticSyntax (stx : Syntax) : EvalResult Unit :=
  match findQuestionTacticKind stx with
  | some kind => .error (.forbiddenTactic kind)
  | none => .ok ()

def withTimeout {α : Type} (timeout : Nat) (act : TacticM α) : TacticM (Option α) := do
  let deadline := (← IO.monoMsNow) + timeout
  let (cancel, task) ← TacticM.asTask act
  while (← IO.monoMsNow) <= deadline do
    if ← IO.hasFinished task then return some (← task.get)
    IO.sleep 1000
  cancel
  return none

def runTacticSyntax (stx : Syntax) (heartbeats : Nat) (timeout : Nat) : TacticM (EvalResult (List Message)) := do
  match ← withTimeout timeout (withCapturedMessages do
    withCatchRuntime do
      withHeartbeats heartbeats <| evalTactic stx
      Term.synthesizeSyntheticMVarsNoPostponing
      pruneSolvedGoals
      return .ok ()) with
  | some (result, messages) => return result.map fun _ => messages
  | none => return .error .tacticTimeout

def checkMessages (messages : List Message) : TacticM (EvalResult Unit) := do
  if hasErrorMessages messages then
    return .error (.tacticErrorMessages (← messages.filterMapM fun x => if x.severity != .information then x.serialize else return none))
  return .ok ()

def evalTacticStrCore (str : String) (heartbeats : Nat) (checkCtx? : Option ProofCheckContext) : TacticM (EvalResult (Array Name)) := do
  let state := toString <| ← TacticGenerator.Meta.ppProofState (← getGoals)
  appendLogRecord (json%{
    name: "tactic_eval_pre",
    start: $(← IO.monoNanosNow.toIO),
    extra: { state: $state, tactic: $str }
  })
  withLogWallClockTime "tactic_eval" (fun result => json%{ state: $state, tactic: $str, result: $result }) <| ExceptT.run do
    let stx ← parseTacticStr str
    checkTacticSyntax stx
    let usedPremise ← collectExplicitConstNames stx
    let messages ← runTacticSyntax stx heartbeats (reap.timeout.get (← getOptions))
    checkMessages messages
    if (← getGoals).isEmpty then
      match checkCtx? with
      | some checkCtx => checkProof checkCtx
      | none => pure ()
    return usedPremise

def evalTacticStr (ctx : ProofCheckContext) (str : String) (heartbeats : Nat) : TacticM (EvalResult (Array Name)) :=
  evalTacticStrCore str heartbeats (some ctx)

def evalTacticStrNoFinalCheck (_ctx : ProofCheckContext) (str : String) (heartbeats : Nat) : TacticM (EvalResult (Array Name)) :=
  evalTacticStrCore str heartbeats none

end Reap.TreeSearch
