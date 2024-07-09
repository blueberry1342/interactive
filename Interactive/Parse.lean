import Lean

open Lean Parser Elab.Tactic

variable {m : Type _ → Type _} [Monad m] [MonadEnv m] [MonadResolveName m] [MonadError m]
def runParserFn
    (fn : ParserFn) (input : String) (filename : String := "<input>") : m Syntax := do
  let env ← getEnv
  let ictx := mkInputContext input filename
  let pmctx := {
    env,
    options := .empty,
    currNamespace := ← getCurrNamespace,
    openDecls := ← getOpenDecls,
  }
  let result := fn.run ictx pmctx (getTokenTable env) {
    cache := initCacheForInput input,
    pos := 0
  }
  if let some message := result.errorMsg then
    throwError message.toString
  return result.stxStack.back

def parseTerm : String → m Syntax := runParserFn termParser.fn
