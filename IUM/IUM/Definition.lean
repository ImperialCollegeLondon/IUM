import Verbose.Tactics.Lets

/-- Our copy of the natural numbers called `MyNat`, with notation `ℕ`. -/
inductive MyNat where
| zero : MyNat
| succ : MyNat → MyNat

export MyNat (zero succ)

attribute [pp_nodot] succ

@[inherit_doc]
notation (name := MyNatNotation) (priority := 1000000) "ℕ" => MyNat
-- Note: as long as we do not import `Mathlib.Init.Data.Nat.Notation` this is fine.

namespace MyNat

instance : OfNat MyNat 0 := ⟨zero⟩
instance : OfNat MyNat 1 := ⟨succ 0⟩
instance : OfNat MyNat 2 := ⟨succ 1⟩
instance : OfNat MyNat 3 := ⟨succ 2⟩
instance : OfNat MyNat 4 := ⟨succ 3⟩

attribute [default_instance] MyNat.instOfNatOfNatNat
attribute [default_instance] MyNat.instOfNatOfNatNat_1
attribute [default_instance] MyNat.instOfNatOfNatNat_2

open Lean Meta Elab Tactic Mathlib.Tactic

/-- Recursion principle for `MyNat` in which we use the notation `0`, rather than `.zero`, and the
case names `BaseCase` and `InductiveStep`, rather than `zero` and `succ`. -/
def MyNat.rec' {motive : ℕ → Sort*} (BaseCase : motive 0)
    (InductiveStep : ∀ a : ℕ, motive a → motive (succ a)) :
    ∀ t : ℕ, motive t
  | .zero => BaseCase
  | .succ k => InductiveStep k (MyNat.rec' BaseCase InductiveStep k)

/-- This tactic sets up a proof by induction on the specified `MyNat` variable. -/
elab "Let's" " prove this by induction on" tgt:ident : tactic => do
  let tgt : Expr ← elabTerm tgt none
  liftMetaTactic fun g ↦ do
    let #[base, induct] ← g.induction tgt.fvarId! ``MyNat.rec' | failure
    let #[k, IH] := induct.fields | failure
    let inductMvarDecl ← induct.mvarId.getDecl
    let mut lctx  := inductMvarDecl.lctx
    lctx := lctx.setUserName k.fvarId! (← mkFreshUserName `k)
    lctx := lctx.setUserName IH.fvarId! (← mkFreshUserName `IH)
    let inductRenamed ← mkFreshExprMVarAt lctx inductMvarDecl.localInstances inductMvarDecl.type
      MetavarKind.syntheticOpaque inductMvarDecl.userName
    let (_, inductNew) ← inductRenamed.mvarId!.revert #[IH.fvarId!, k.fvarId!]
    induct.mvarId.assign inductRenamed
    pure [base.mvarId, inductNew]
