import Analyzer.Goal
import Interactive.JsonRpc
import Lean.Elab.Tactic
import Lean.Elab.Frontend

open Lean Core Meta Elab Command Tactic

namespace Interactive.Handler
open JsonRpc

structure Node where
  tacticState : Tactic.SavedState
  parent : Nat
  tactic : String

abbrev State := Array Node

variable {m : Type _ → Type _} [Monad m] [MonadState State m]

private def push (n : Node) : m Unit :=
  modify (·.push n )

private def gets [MonadExceptOf Error m] (sid : Nat) : m Node := do
  match (← get)[sid]? with
  | .some n => return n
  | .none => throw <| invalidParams "sid out of range"

abbrev HandlerM := StateT State (ExceptT Error TacticM)

instance : MonadLift IO HandlerM where
  monadLift := liftM

open MonadExceptOf -- for throw

def initialState : TacticM State := do
  pruneSolvedGoals
  let s ← Tactic.saveState
  return Array.mkArray1 ⟨ s, 0, "" ⟩

def runHandlerM {α : Type _} (handler : HandlerM α) (s : State) : TacticM α := do
  match ← (handler.run' s).run with
  | .ok r => return r
  | .error e => throwNestedTacticEx `Interactive <| .error (← getRef) (.ofFormat (.text e.message))

instance : MonadHandler HandlerM where
  runTactic sid tactic := do
    let ts := (← gets sid).tacticState
    ts.restore
    match Parser.runParserCategory (← getEnv) `tactic tactic with
    | .error e => throw $ Error.mk 0 "Lean parser error" e
    | .ok stx =>
      try
        evalTactic stx
      catch e =>
        throw $ Error.mk 1 "Tactic error" (← e.toMessageData.toString)
        ts.restore
      let s ← getThe Core.State
      if s.messages.hasErrors then
        let ms ← liftM $ s.messages.toList.mapM Message.toString
        throw <| Error.mk 1 "Tactic error" <| some <| toJson ms
      pruneSolvedGoals
      let i := (← get).size
      push { tacticState := ← Tactic.saveState, parent := sid, tactic }
      return i

  getState sid := do
    (← gets sid).tacticState.restore
    let goals ← getGoals
    let .some mainGoal := goals.head? | return .none
    let goal ← Analyzer.Goal.fromMVar mainGoal
    return .some { mainGoal := goal, numGoals := goals.length }

  getMessages sid := do
    (← gets sid).tacticState.restore
    let messages ← getMessageLog
    messages.msgs.toArray.mapM fun m => m.serialize

  resolveName sid name := do
    (← gets sid).tacticState.restore
    return (← resolveGlobalName (.mkSimple name))

  getPosition := do
    let pos := (← getRef).getPos?
    let fileMap ← getFileMap
    return pos.map fileMap.toPosition
  commit _sid := pure ()
  giveUp := pure ()

end Interactive.Handler
