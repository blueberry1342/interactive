import Lean

open Lean Elab

inductive Selector where
  | byPos : String.Pos → Selector
  | byId : Name → Selector

def Selector.match (stx : Syntax) (defView : DefView) : Selector → Bool
  | byPos pos => Option.isSome do
      let startPos ← stx.getPos?
      let endPos ← stx.getTailPos?
      guard $ startPos <= pos && pos <= endPos
      return
  | byId name => name == defView.declId[0].getId
