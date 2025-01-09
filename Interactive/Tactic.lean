import Lean.Elab.Tactic
import Interactive.JsonRpc
import Interactive.Handler

open Lean Elab Tactic Term

namespace Interactive
open Handler

protected def tactic : Tactic := fun _ => do
  let declName ← getDeclName?
  IO.println <| json%{ declName: $(declName) }.compress
  (← IO.getStdout).flush
  let state ← initialState
  runHandlerM Handler.loop state

end Interactive
