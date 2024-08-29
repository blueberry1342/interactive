import Lean.Elab.Tactic
import Interactive.JsonRpc
import Interactive.Handler

open Lean.Elab.Tactic

namespace Interactive
open Handler

protected def tactic : Tactic := fun _ => do
  let state ← initialState
  runHandlerM Handler.loop state

end Interactive
