import Analyzer.Goal
import Analyzer.Types
import Analyzer.Output
import Batteries
import Lean

open Lean

namespace Interactive.JsonRpc

structure Request where
  id: Int
  method: String
  params: Json
deriving FromJson

structure Error where
  code: Int
  message: String
  data?: Option Json
deriving ToJson

structure Response where
  id: Option Int
  result? : Option Json := none
  error?: Option Error := none
deriving ToJson

deriving instance ToJson for Position

namespace Response

def mkEmptyResult (id : Int) : Response :=
  ⟨ some id, some Json.null, none ⟩

def mkResult {α : Type _} [ToJson α] (id : Int) (result : α) : Response :=
  ⟨ some id, some <| toJson result, none ⟩

def mkError (id : Int) (error : Error) : Response :=
  ⟨ some id, none, some error ⟩

end Response

def parseError (e : Option String) : Error := ⟨ -32700, "Parse error", e ⟩
def invalidRequest (e : Option String) : Error := ⟨ -32600, "Invalid request", e ⟩
def methodNotFound (e : Option String) : Error := ⟨ -32601, "Method not found", e ⟩
def invalidParams (e : Option String) : Error := ⟨ -32602, "Invalid params", e ⟩


def firstLetterCaptial (name : String) : String :=
  (name.get 0).toUpper.toString ++ name.drop 1

def getParamsAndResult (handler : Name) (method : Name) : CoreM (Array (Name × Expr) × Expr) := do
  let type := ((← getEnv).find? (handler ++ method)).get!.type
  let rec loop (params : Array (Name × Expr)) (type : Expr) :=
    match type with
    | .forallE n t b .default => loop (params.push (n, t)) b
    | .forallE _ _ b _ => loop params b
    | e => (params, e)
  return loop #[] type

open private mkProjections from Lean.Elab.Structure
def addStruct (name : Name) (fields : Array (Name × Expr)) : CoreM Unit := do
  let type := mkSort 1
  let ctorType : Expr := .const name []
  let ctorType := fields.foldr (fun (n, t) e => .forallE n t e .default) ctorType
  let ctors := [{name := name ++ `mk, type := ctorType}]
  let structureDescr := {
    structName := name,
    fields := fields.map (fun (p, _) => ⟨p, name ++ p, none, .default, none⟩)
  }
  addDecl (mkInductiveDeclEs [] 0 [{name, type, ctors}] false)
  let env := registerStructure (← getEnv) structureDescr
  let env ← ofExceptKernelException $
    mkProjections env name (structureDescr.fields.toList.map (·.projFn)) false
  setEnv env

syntax (name := register_handler) "register_handler" ident : command

set_option hygiene false in
open Elab Command Parser.Term in
@[command_elab «register_handler»] def elabRegisterHandler : CommandElab
| `(register_handler $handler:ident) => do
  let (handler, _) := (← resolveGlobalName handler.getId)[0]!
  let names := getStructureFieldsFlattened (← getEnv) handler false
  let mut doElems := #[]
  for name in names do
    let (params, result) ← liftCoreM $ getParamsAndResult handler name
    let fnName := mkIdent (handler ++ name)
    let paramNames := params.map (fun p => mkIdent (`params ++ p.1))
    let paramStructure : Ident := mkIdent <| .mkSimple (firstLetterCaptial name.toString ++ "Params")
    let structureName := mkPrivateName (← getEnv) ((← expandDeclId paramStructure {}).declName)
    let registerParamStructure := do
      liftCoreM $ addStruct structureName params
      elabCommand (← `(deriving instance FromJson for $(mkIdent structureName)))
    let handleRequestForMethod : CommandElabM (TSyntax ``doSeqItem) := do
      let nonemptyResult := match result with
      | .app (.bvar _) (.const `Unit _) => false
      | .app (.bvar _) (.const `PUnit _) => false
      | _ => true
      let mkResult ← if nonemptyResult then `(.mkResult req.id result) else `(.mkEmptyResult req.id)
      if params.size > 0 then `(doSeqItem |
        if req.method == $(Syntax.mkStrLit name.getString!) then
          match (fromJson? req.params : Except String $paramStructure) with
          | .ok params =>
            let result ← ($(Syntax.mkApp fnName paramNames))
            return $mkResult
          | .error e =>
            return .mkError req.id <| invalidParams e)
      else `(doSeqItem |
        if req.method == $(Syntax.mkStrLit name.getString!) then
          let result ← ($(Syntax.mkApp fnName paramNames))
          return $mkResult)
    if params.size > 0 then registerParamStructure
    doElems := doElems.push (← handleRequestForMethod)
  doElems := doElems.push (← `(doSeqItem | return .mkError req.id <| methodNotFound req.method))
  let stx ← `(private def handleRequest
    {m : Type _ → Type _} [Monad m] [MonadExceptOf Error m] [MonadHandler m] (req : Request)
    : m Response := do $[$doElems]*)
  elabCommand stx
| _ => throwUnsupportedSyntax

end Interactive.JsonRpc
