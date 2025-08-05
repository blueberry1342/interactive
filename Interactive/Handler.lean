import Lean
import Metalib.Parse
import Analyzer.Goal
import Interactive.JsonRpc
import Interactive.Unify

open Lean Core Meta Elab Command Tactic

namespace Interactive.Handler
open JsonRpc

structure ProofVariable where
  name : Name
  type : String
deriving FromJson

structure ProofGoal where
  context : Array ProofVariable
  type : String
deriving FromJson

structure CommitInfo where
  errorcode : Nat
  correctness: Option String := none
deriving ToJson

class MonadHandler (m : Type _ → Type _) [Monad m] [MonadExceptOf Error m] where
  /-- returns a new state id.
  this method can be async or lazy, i.e., the new state might not be ready yet -/
  runTactic : (sid : Nat) → (tactic : String) → (heartbeats : Nat) → m Nat

  /-- returns pretty-printed main goal and number of goals of the given state id -/
  getState : (sid : Nat) → m (Array Analyzer.Goal)

  getMessages : (sid : Nat) → m (Array SerialMessage)

  /-- returns a list of possible interpretations along with field names -/
  resolveName : (sid : Nat) → (name : String) → m (List (Name × List String))

  /-- tries to unify two terms, returning a solution if possible -/
  unify : (sid : Nat) → (s1 s2 : String) → m (Option (Array (Name × Option String)))

  /-- creates a new state from user input -/
  newState : (state : List ProofGoal) → m Nat

  getPosition : m (Option Position)

  /-- admit all goals -/
  giveUp : (sid : Nat) → m Nat

  /-- ends the tactic execution -/
  commit : (sid : Nat) → m CommitInfo

register_handler MonadHandler handleRequest

variable {m : Type _ → Type _} [Monad m] [MonadExceptOf Error m] [MonadHandler m] (req : Request)

protected def handleLine [MonadLift IO m]: m Unit := do
  let line ← (← IO.getStdin).getLine
  let response ← match Json.parse line with
  | .ok json =>
    match (fromJson? json : Except String Request) with
    | .ok req =>
      try
        handleRequest req
      catch e =>
        pure <| Response.mkError req.id e
    | .error e =>
      pure ⟨ none, none, some <| invalidRequest e ⟩
  | .error e =>
    pure ⟨ none, none, some <| parseError e ⟩
  IO.println (toJson response).compress
  (← IO.getStdout).flush


structure Node where
  tacticState : Tactic.SavedState
  parent : Nat
  tactic : String

structure State where
  nodes : Array Node
  running : Bool

variable {m : Type _ → Type _} [Monad m] [MonadState State m]

private def push (n : Node) : m Unit :=
  modify fun s => { s with nodes := s.nodes.push n }

private def gets [MonadExceptOf Error m] (sid : Nat) : m Node := do
  match (← get).nodes[sid]? with
  | .some n => return n
  | .none => throw <| invalidParams "sid out of range"

abbrev HandlerM := StateT State (ExceptT Error TacticM)

instance : MonadLift IO HandlerM where
  monadLift := liftM

open MonadExceptOf -- for throw

def initialState : TacticM State := do
  pruneSolvedGoals
  let s ← Tactic.saveState
  return {
    nodes := Array.mkArray1 ⟨ s, 0, "" ⟩,
    running := true,
  }

def runHandlerM {α : Type _} (handler : HandlerM α) (s : State) : TacticM α := do
  match ← (handler.run' s).run with
  | .ok r => return r
  | .error e => throwNestedTacticEx `Interactive <| .error (← getRef) (.ofFormat (.text e.message))

def saveAsNewNode (parent : Nat) (tactic : String) : HandlerM Nat := do
  pruneSolvedGoals
  let i := (← get).nodes.size
  push {
    tacticState := ← Tactic.saveState,
    parent,
    tactic,
  }
  return i

def withHeartbeats {α : Type _} [Monad m] [MonadWithReaderOf Core.Context m] (heartbeats : Nat) : m α → m α :=
  withReader (fun s => { s with maxHeartbeats := heartbeats })

def collectFVarsAux : Expr → NameSet
  | .fvar fvarId => NameSet.empty.insert fvarId.name
  | .app fm arg => (collectFVarsAux fm).union $ collectFVarsAux arg
  | .lam _ binderType body _ => (collectFVarsAux binderType).union $ collectFVarsAux body
  | .forallE _ binderType body _ => (collectFVarsAux binderType).union $ collectFVarsAux body
  | .letE _ type value body _ => ((collectFVarsAux type).union $ collectFVarsAux value).union $ collectFVarsAux body
  | .mdata _ expr => collectFVarsAux expr
  | .proj _ _ struct => collectFVarsAux struct
  | _ => NameSet.empty

def collectFVars (e : Expr) : MetaM (Array Expr) := do
  let names := collectFVarsAux e
  let mut fvars := #[]
  for ldecl in ← getLCtx do
    if ldecl.isImplementationDetail then
      continue
    if names.contains ldecl.fvarId.name then
      fvars := fvars.push $ .fvar ldecl.fvarId
  return fvars

def abstractAllLambdaFVars (e : Expr) : MetaM Expr := do
  let mut e' := e
  while e'.hasFVar do
    let fvars ← collectFVars e'
    if fvars.isEmpty then
      break
    e' ← mkLambdaFVars fvars e'
  return e'

private def collectFromLevel : Level → NameSet
| Level.zero => NameSet.empty
| Level.succ l => collectFromLevel l
| Level.param n => NameSet.empty.insert n
| Level.max l1 l2 => (collectFromLevel l1).union $ collectFromLevel l2
| Level.imax l1 l2 => (collectFromLevel l1).union $ collectFromLevel l2
| Level.mvar _ => NameSet.empty

private def levels2Names : List Level → NameSet
  | [] => NameSet.empty
  | Level.param n :: us => (levels2Names us).insert n
  | _ :: us => levels2Names us

def collectLevelParams : Expr → NameSet
  | .sort u => collectFromLevel u
  | .const _ us => levels2Names us
  | .app fm arg => (collectLevelParams fm).union $ collectLevelParams arg
  | .lam _ binderType body _ => (collectLevelParams binderType).union $ collectLevelParams body
  | .forallE _ binderType body _ => (collectLevelParams binderType).union $ collectLevelParams body
  | .letE _ type value body _ => ((collectLevelParams type).union $ collectLevelParams value).union $ collectLevelParams body
  | .mdata _ expr => collectLevelParams expr
  | .proj _ _ struct => collectLevelParams struct
  | _ => NameSet.empty


instance : MonadHandler HandlerM where
  runTactic sid tactic heartbeats := do
    let ts := (← gets sid).tacticState
    ts.restore
    match Parser.runParserCategory (← getEnv) `tactic tactic with
    | .error e => throw <| Error.mk 0 "Lean parser error" e
    | .ok stx =>

      let handler (e : Exception) : TacticM (Except Error Unit) := do
        ts.restore
        return .error <| .mk 1 "Tactic error" (← e.toMessageData.toString)
      ExceptT.mk <| tryCatchRuntimeEx (handler := handler) <|
        MonadExcept.tryCatch (do
          withHeartbeats heartbeats <| evalTactic stx
          return .ok ()
        ) handler

      let s ← getThe Core.State
      if s.messages.hasErrors then
        let ms ← liftM $ s.messages.toList.mapM Message.toString
        throw <| Error.mk 1 "Tactic error" <| some <| toJson ms
    saveAsNewNode sid tactic

  getState sid := do
    (← gets sid).tacticState.restore
    let goals ← getGoals
    goals.toArray.mapM fun goal => Analyzer.Goal.fromMVar goal

  getMessages sid := do
    (← gets sid).tacticState.restore
    let messages ← getMessageLog
    messages.toArray.mapM fun m => m.serialize

  resolveName sid name := do
    (← gets sid).tacticState.restore
    return (← resolveGlobalName (.mkSimple name))

  unify sid s₁ s₂ := do
    (← gets sid).tacticState.restore
    let (stx₁, stx₂) ← try
      pure (← parseTerm s₁, ← parseTerm s₂)
    catch e =>
      throw <| Error.mk 2 "Parse error" (← e.toMessageData.toString)
    try
      unify stx₁ stx₂
    catch e =>
      throw <| Error.mk 3 "Elaboration error" (← e.toMessageData.toString)

  newState goals := withLCtx .empty #[] do
    let gs ← goals.mapM fun g => parseGoal (g.context.map fun v => (v.name, v.type)) .anonymous g.type
    setGoals gs
    saveAsNewNode 0 ""

  getPosition := do
    let pos := (← getRef).getPos?
    let fileMap ← getFileMap
    return pos.map fileMap.toPosition

  giveUp sid := do
    (← gets sid).tacticState.restore
    for goal in ← getGoals do
      goal.admit
    saveAsNewNode sid ""

  commit sid := do
    match (← get).nodes[sid]? with
    | none => throwError s!"State {sid} not found"
    | some node =>
      let ts := node.tacticState
      match (← get).nodes[0]? with
      | none => throwError "Initial state not found"
      | some node0 =>
        let ts0 := node0.tacticState

        -- Go to the initial state and grab the goal's metavariable ID.
        ts0.restore
        let [goalId] ← getGoals | throwError "[fatal] More than one initial goal"
        let tgt ← getMainTarget >>= instantiateMVars
        let tgt_fmt ← ppExpr tgt

        -- Check its assigned Expr in the current state.
        ts.restore
        let some pf ← getExprMVarAssignment? goalId | throwError "[fatal] goal not assigned"
        let pf ← instantiateMVars pf
        let pft ← inferType pf >>= instantiateMVars
        let pft_fmt ← ppExpr pft

        if ! (← withTransparency .all (isExprDefEq tgt pft)) then
          (← gets sid).tacticState.restore
          modify fun s => { s with running := false }
          return {errorcode := Nat.zero.succ, correctness := s!"Proof type mismatch: {tgt_fmt} != {pft_fmt}"}

        ts0.restore
        let pf ← goalId.withContext $ abstractAllLambdaFVars pf
        let pft ← inferType pf >>= instantiateMVars

        ts.restore
        if pf.hasSorry then
          (← gets sid).tacticState.restore
          modify fun s => { s with running := false }
          return {errorcode := Nat.zero.succ.succ, correctness := "Proof contains `sorry`"}

        if pf.hasExprMVar then
          (← gets sid).tacticState.restore
          modify fun s => { s with running := false }
          return {errorcode := Nat.zero.succ.succ.succ, correctness := "Proof contains metavariables"}

        -- Kernel type check.
        let lvls := (collectLevelParams pf).toList
        let decl := Declaration.thmDecl {
            name := Name.anonymous, type := pft, value := pf
            levelParams := lvls
        }
        try
          let _ ← addDecl decl
        catch ex =>
          (← gets sid).tacticState.restore
          modify fun s => { s with running := false }
          return {errorcode := Nat.zero.succ.succ.succ.succ, correctness := s!"Kernel type check failed: {← ex.toMessageData.toString}"}

        (← gets sid).tacticState.restore
        modify fun s => { s with running := false }
        return {errorcode := Nat.zero, correctness := "Proof type correct"}

protected def loop : HandlerM Unit := do
  while (← get).running do
    Handler.handleLine

end Interactive.Handler
