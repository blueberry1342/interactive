import Lean

open Lean Meta Elab Term Command

def unify (stx₁ stx₂ : Syntax) : MetaM (Option (Array (Name × Option String))) := do
  let context := {
    mayPostpone := false,
    errToSorry := false,
    implicitLambda := false,
  : Elab.Term.Context}
  let elabTerm' := fun stx => elabTerm stx none |>.run' (ctx := context)
  let (expr₁, expr₂) ← try
    pure (← elabTerm' stx₁, ← elabTerm' stx₂)
  catch e =>
    throwError (← e.toMessageData.toString)
  let mvars := (← (← getMVars expr₁) ++ (← getMVars expr₂)
    |>.mapM fun mvar => do pure (← mvar.getTag, mvar))
    |>.filter fun (name, _) => !name.isAnonymous
  mvars.forM fun (_, mvar) => mvar.setKind .synthetic
  if ← isDefEqGuarded expr₁ expr₂ then
    return some (
      ← mvars.mapM fun (name, mvar) => do
        let value ← getExprMVarAssignment? mvar
        let value ← value.mapM fun value => do pure (← ppExpr value).pretty
        pure (name, value)
    )
  else
    return none
