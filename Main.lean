import Lean
import Cli
import Metalib.Load
import Interactive.Load

open Lean Elab Frontend Cli System

unsafe def runCommand (p : Parsed) : IO UInt32 := do
  let handleSorry := p.hasFlag "sorry"
  let file := FilePath.mk <| p.positionalArg! "file" |>.as! String
  if p.hasFlag "initializer" then
    enableInitializersExecution
  discard <| withFile file do
    runCommandElabM <| onLoad handleSorry
    Main.loop
  return 0

unsafe def interactiveCommand : Cmd := `[Cli|
  interactive VIA runCommand;
  "Interact with a proof."

  FLAGS:
    s, «sorry»;  "Turn sorries into interactive points"
    i, initializer;  "Execute initializers"

  ARGS:
    file : String;  "File to interact with"
]

unsafe def main : List String → IO UInt32 :=
  interactiveCommand.validate
