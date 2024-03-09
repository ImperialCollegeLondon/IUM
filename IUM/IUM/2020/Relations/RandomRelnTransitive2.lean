import Mathbin.Tactic.Default

#align_import «2020».relations.random_reln_transitive2

namespace RandomRelnTransitive2

-- Let X be the set {A,B,C}
inductive X
  | A : X
  | B : X
  | C : X

open X

def R (x y : X) : Prop :=
  x = A ∧ y = B ∨ x = A ∧ y = C

-- R(A,B) and R(A,C) both true, everything else false
theorem r_fst {x y : X} : R x y → x = A := by
  intro h
  cases h
  cases h
  assumption
  cases h
  assumption

example : Transitive R := by
  intro x y z
  intro hxy
  intro hyz
  have h1 := R_fst hxy
  have h2 := R_fst hyz
  subst h1
  subst h2
  assumption

example (P Q : Prop) : (P → Q) → ¬Q → ¬P := by
  intro hPQ
  intro hnQ
  intro hP
  apply hnQ
  exact hPQ hP

end RandomRelnTransitive2

