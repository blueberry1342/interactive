import Lean
import Cli
import Analyzer.Load
import Interactive.Load

open Lean Elab Frontend Cli System

def parseSelector (p : Parsed) : Option Selector :=
  (p.flag? "pos" |>.map fun f => .byPos ⟨f.as! Nat⟩) <|>
  (p.flag? "id" |>.map fun f => .byId <| f.as! String |>.toName)

def runCommand (p : Parsed) : IO UInt32 := do
  let selector := parseSelector p
  let handleSorry := p.hasFlag "sorry"
  if selector.isNone && !handleSorry then
    IO.eprintln "no selector specified and not handling sorry"
    return 0
  let file := FilePath.mk <| p.positionalArg! "file" |>.as! String
  Analyzer.withFile' file do
    runCommandElabM <| onLoad selector handleSorry
    processCommands
    let messages := (← get).commandState.messages
    for message in messages.msgs do
      IO.println (← message.toString)
  return 0

def interactiveCommand : Cmd := `[Cli|
  interactive VIA runCommand;
  "Interact with a proof."

  FLAGS:
    p, pos : Nat;  "Byte index"
    d, id : String;  "Declaration id"
    s, «sorry»;  "Turn sorries into interactive points"

  ARGS:
    file : String;  "File to interact with"
]

def main : List String → IO UInt32 :=
  interactiveCommand.validate
