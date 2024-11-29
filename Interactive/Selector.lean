import Lean

open Lean Elab

inductive Selector where
  | all : Selector
  | byPos : String.Pos → Selector
  | byId : Name → Selector

instance : FromJson Selector where
  fromJson?
    | .null => .ok .all
    | s => (Selector.byPos ∘ .mk) <$> s.getNat? <|> (Selector.byId ∘ .mkSimple) <$> s.getStr?

def Selector.match (stx : Syntax) (defView : DefView) : Selector → Bool
  | all => true
  | byPos pos => Option.isSome do
      let startPos ← stx.getPos?
      let endPos ← stx.getTailPos?
      guard $ startPos <= pos && pos <= endPos
      return
  | byId name => name == defView.declId[0].getId
