import Mathlib.Tactic.DefEqTransformations

open Lean Elab Tactic Meta

def Lean.Expr.clearMDataRec : Expr → Expr
  | .app fn arg => .app fn.clearMDataRec arg.clearMDataRec
  | .proj typeName idx struct => .proj typeName idx struct.clearMDataRec
  | .mdata _ e => e.clearMDataRec
  | .letE declName type value body nondep =>
    .letE declName type.clearMDataRec value.clearMDataRec body.clearMDataRec nondep
  | .forallE binderName binderType body binderInfo =>
    .forallE binderName binderType.clearMDataRec body.clearMDataRec binderInfo
  | .lam binderName binderType body binderInfo =>
    .lam binderName binderType.clearMDataRec body.clearMDataRec binderInfo
  | e@_ => e

def applyDef (decl : Name) (g : MVarId) : MetaM Unit := do
  let some eqThms ← getEqnsFor? decl | failure
  let ty ← instantiateMVars (← g.getType)
  let tyRed ← Mathlib.Tactic.unfoldProjs ty.clearMDataRec
  trace[debug] "type {ty}, reduced to {tyRed}"
  let s ← saveState
  for thmName in eqThms do
    s.restore
    let thm ← mkConstWithFreshMVarLevels thmName
    trace[debug] "running with {thm}"
    let e ← inferType thm
    let (_, _, e) ← forallMetaTelescopeReducing e
    trace[debug] "picked out {e}, going to unify with {tyRed}"
    if ← withReducible <| isDefEq e tyRed then
      trace[debug] "successful unification"
      let e ← instantiateMVars e
      if e.clearMDataRec == tyRed.clearMDataRec then
        g.applyRfl
        return
  failure

def applyDefWithSymm (decl : Name) (g : MVarId) : MetaM Unit := do
  try
    applyDef decl g
  catch _ =>
    applyDef decl (← g.applySymm)

def applyDefTactic (id : TSyntax `ident) : TacticM Unit := do
  let declName ← realizeGlobalConstNoOverload id
  liftMetaFinishingTactic (applyDefWithSymm declName)

elab "apply_def" id:ident : tactic => applyDefTactic id
elab "definition" " of" id:ident : tactic => applyDefTactic id
elab "Apply" " definition" " of" id:ident : tactic => applyDefTactic id
