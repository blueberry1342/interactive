import Lean
import Interactive.Tactic
import Interactive.Selector

open Lean Elab Command Tactic

syntax "interactive" : tactic

initialize matched : IO.Ref Bool ← IO.mkRef false

def handleDeclaration (selector : Selector) (stx : Syntax) : CommandElabM Unit := do
  let modifiers ← elabModifiers stx[0]
  let decl := stx[1]
  if isDefLike decl then
    let defView ← mkDefView modifiers decl
    if selector.match stx defView then
      matched.set true
      let node ← `(by interactive)
      let defView := { defView with value := defView.value.setArg 1 node }
      runTermElabM fun vars => Term.elabMutualDef vars #[defView]
      return

  throwUnsupportedSyntax

def onLoad (selector : Option Selector) (handleSorry : Bool := false) : CommandElabM Unit := do
  let cmd ← `(syntax "interactive" : $(mkIdent `tactic))
  elabCommand cmd
  if handleSorry then
    let cmd ← `(syntax (name := $(mkIdent `tacticInteractive)) "sorry" : $(mkIdent `tactic))
    elabCommand cmd
  modifyEnv fun env => tacticElabAttribute.ext.addEntry env {
    key := `tacticInteractive,
    declName := ``Interactive.tactic,
    value := Interactive.tactic,
  }
  if let some selector := selector then
    modifyEnv fun env => commandElabAttribute.ext.addEntry env {
      key := ``Parser.Command.declaration,
      declName := ``handleDeclaration,
      value := handleDeclaration selector,
    }
