import Lean
import Interactive.JsonRpc
import Interactive.Tactic
import Interactive.Selector

open Lean Elab Frontend Command Tactic

syntax "interactive" : tactic

initialize selectorsRef : IO.Ref (Array Selector) ← IO.mkRef #[]

def handleDeclaration (stx : Syntax) : CommandElabM Unit := do
  let modifiers ← elabModifiers stx[0]
  let decl := stx[1]
  if isDefLike decl then
    let defView ← mkDefView modifiers decl
    if (← selectorsRef.get).any <| fun s => s.match stx defView then
      let node ← `(by interactive)
      let scope ← getScope
      let defView := { defView with value := defView.value.setArg 1 node }
      runTermElabM fun vars => Term.elabMutualDef vars scope #[defView]
      return

  throwUnsupportedSyntax

def onLoad (handleSorry : Bool := false) : CommandElabM Unit := do
  let cmd ← `(set_option maxHeartbeats 0)
  elabCommand cmd
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
  modifyEnv fun env => commandElabAttribute.ext.addEntry env {
    key := ``Parser.Command.declaration,
    declName := ``handleDeclaration,
    value := handleDeclaration,
  }

open System Parser in
def loadFileIgnoreHeader (path : FilePath) : IO (InputContext × ModuleParserState) := do
  let input ← IO.FS.readFile path
  let inputCtx := mkInputContext input path.toString
  let (_, parserState, _) ← parseHeader inputCtx
  return (inputCtx, parserState)

namespace Main

protected def loop : Frontend.FrontendM Unit := do
  while true do
    let line ← (← IO.getStdin).getLine
    let request := show Except _ _ from do
      let request ← Json.parse line
      let filename ← (← request.getObjVal? "filename").getStr?
      let filename := System.FilePath.mk filename
      let selectors ← (← request.getObjVal? "selectors").getArr?
      let selectors ← selectors.mapM fun s => fromJson? s
      pure (filename, selectors)

    if let .ok (filename, selectors) := request then
      selectorsRef.set selectors
      let (context, parserState) ← Frontend.runCommandElabM <| loadFileIgnoreHeader filename
      discard <| processCommands { inputCtx := context } |>.run {
        commandState := (← get).commandState,
        parserState := parserState,
        cmdPos := parserState.pos,
      }
      IO.println "{}"
      (← IO.getStdout).flush
    else
      break

end Main
