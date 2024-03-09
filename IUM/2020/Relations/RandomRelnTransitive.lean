import Mathbin.Tactic.Default

#align_import «2020».relations.random_reln_transitive

-- Let X be the set {A,B,C}
-- Let X be the set {A,B,C}
inductive X
  | A : X
  | B : X
  | C : X
  deriving Fintype

open X

inductive R : X → X → Prop
  | AB : R A B
  | AC : R A C

instance : DecidableRel R := by
  unfold DecidableRel
  intro a b
  cases a <;> cases b <;> [left; right; right; left; left; left; left; left; left] <;>
    first
    | exact R.AB
    | exact R.AC
    | rintro (_ | _)

instance : Decidable (Transitive R) := by
  unfold Transitive
  infer_instance

theorem r_fst {x y : X} : R x y → x = A := by rintro (hAB | hAC) <;> rfl

example : Transitive R := by decide

-- human proof below
-- intros p q r,
-- intros hpq hqr,
-- have hp := R_fst hpq,
-- subst hp,
-- have hq := R_fst hqr,
-- subst hq,
-- assumption,
