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
  | tacticErrorMessages (messages : List String)
  | assignedProofHasMVarOrSorry
  | auxProofHasMVarOrSorry (declName : Name)
  | auxProofKernelCheckFailed (declName : Name) (message : String)
  | finalProofCheckFailed

namespace EvalError

def kind : EvalError → String
  | .parseError _ => "parse_error"
  | .forbiddenTactic _ => "forbidden_tactic"
  | .tacticException _ => "tactic_exception"
  | .tacticErrorMessages _ => "tactic_error_messages"
  | .assignedProofHasMVarOrSorry => "assigned_proof_has_mvar_or_sorry"
  | .auxProofHasMVarOrSorry _ => "aux_proof_has_mvar_or_sorry"
  | .auxProofKernelCheckFailed _ _ => "aux_proof_kernel_check_failed"
  | .finalProofCheckFailed => "final_proof_check_failed"

def toString : EvalError → String
  | .parseError message => message
  | .forbiddenTactic kind => s!"forbidden tactic syntax: {kind}"
  | .tacticException message => message
  | .tacticErrorMessages messages => String.intercalate "\n" messages
  | .assignedProofHasMVarOrSorry => "assigned proof contains a metavariable or sorry"
  | .auxProofHasMVarOrSorry declName => s!"auxiliary proof {declName} contains a metavariable or sorry"
  | .auxProofKernelCheckFailed declName message => s!"auxiliary proof {declName} failed kernel check:\n{message}"
  | .finalProofCheckFailed => "final proof check failed"

instance : ToString EvalError := ⟨toString⟩

end EvalError

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

def checkProof (ctx : ProofCheckContext) : TacticM Bool := do
  for g in ctx.originalGoals do
    if ← g.isAssigned then
      let e ← instantiateMVars (mkMVar g)
      if e.hasSorry || e.hasExprMVar then
        return False

  let mut preDefs := #[]
  for goal in ctx.originalGoals do
    let some preDef ← mkPreDefinition ctx.numSectionFVars goal | return false
    preDefs := preDefs.push preDef
  checkPreDefinitions preDefs

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

partial def checkCurrentAuxDeclsInExpr (parentDeclName : Name) (e : Expr) (checked : Array Name := #[]) : MetaM (Except EvalError (Array Name)) := do
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

def checkAssignedProofs (ctx : ProofCheckContext) : TacticM (Except EvalError Unit) := do
  let some parentDeclName ← Term.getDeclName? | return .ok ()
  let mut checked := #[]
  for goal in ctx.originalGoals do
    if ← goal.isAssigned then
      let value ← instantiateMVars (mkMVar goal)
      if value.hasSorry || value.hasExprMVar then
        return .error .assignedProofHasMVarOrSorry
      match ← goal.withContext <| checkCurrentAuxDeclsInExpr parentDeclName value checked with
      | .ok checked' => checked := checked'
      | .error err => return .error err
  return .ok ()

def isQuestionTacticKind (kind : SyntaxNodeKind) : Bool :=
  kind == `sorry || kind == `admit || (if let .str _ x := kind then x.endsWith "?" else false)

partial def findQuestionTacticKind? (stx : Syntax) : Option SyntaxNodeKind :=
  if isQuestionTacticKind stx.getKind then
    some stx.getKind
  else
    let rec loop (args : Array Syntax) (idx : Nat) : Option SyntaxNodeKind :=
      if h : idx < args.size then
        match findQuestionTacticKind? args[idx] with
        | some kind => some kind
        | none => loop args (idx + 1)
      else
        none
    loop stx.getArgs 0

def messageStrings (messages : List Message) : CoreM (List String) :=
  messages.mapM fun msg => do
    return s!"{msg.severity}: {← msg.data.toString}"

def evalTacticStr (ctx : ProofCheckContext) (str : String) (heartbeats : Nat) : TacticM (Except EvalError Unit) := do
  withLogWallClockTime "tactic_eval" (fun
      | .ok _ => json%{ tactic: $str, success: true }
      | .error err => json%{ tactic: $str, success: false, error_kind: $(err.kind), error: $(toString err) }) do
    let stx ←
      match Parser.runParserCategory (← getEnv) `tactic str with
      | .ok stx => pure stx
      | .error err => return .error (.parseError err)
    if let some kind := findQuestionTacticKind? stx then
      return .error (.forbiddenTactic kind)
    try
      let (result, messages) ← withCapturedMessages do
        try
          tryCatchRuntimeEx (handler := fun ex => do
            return (Except.error (.tacticException (← ex.toMessageData.toString)) : Except EvalError Unit)) do
            withHeartbeats heartbeats do
              evalTactic stx
              Term.synthesizeSyntheticMVarsNoPostponing
            return (Except.ok () : Except EvalError Unit)
        catch ex =>
          return (Except.error (.tacticException (← ex.toMessageData.toString)) : Except EvalError Unit)
      match result with
      | Except.error err => return .error err
      | Except.ok _ =>
        pruneSolvedGoals
        if hasErrorMessages messages then
          return .error (.tacticErrorMessages (← messageStrings messages))
        match ← checkAssignedProofs ctx with
        | .error err => return .error err
        | .ok _ => pure ()
        if (← getGoals).isEmpty then
          if !(← checkProof ctx) then
            return .error .finalProofCheckFailed
    catch ex =>
      return .error (.tacticException (← ex.toMessageData.toString))
    return .ok ()

end Reap.TreeSearch
