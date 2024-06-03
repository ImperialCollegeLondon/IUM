import Mathbin.Tactic.Default

#align_import «2020».logic.logic_video

-- Definition: a Proposition is a type `P`, where `P : Prop`.
-- Definition: a Proposition is a type `P`, where `P : Prop`.
variable (P Q R : Prop)

-- In Lean, `P → Q` means `P ⇒ Q`
example : P → P := by
  intro hP
  -- let hP be the hypothesis that P is true
  exact hP

-- our goal is exactly our hypothesis
example : P → Q → P := by
  intro hP
  -- let hP be the hypothesis that P is true
  intro hQ
  exact hP

-- is → associative? i.e. Does (P → Q) → R equal P → (Q → R) ?
-- (A+B)+C = A+(B+C)  
-- (A-B)-C ≠ A-(B-C)
-- (A-B)-C 
-- 2^(1^3) -- this is the convention for powers
-- CONVENTION: P → Q → R with no brackets MEANS P → (Q → R)
example : P → Q → P := by
  intro hP
  intro hQ
  exact hP

/-- Modus Ponens : if P is true, and P → Q, then Q is true -/
theorem modus_ponens : P → (P → Q) → Q := by
  intro hP
  intro hPQ
  -- hPQ is the hypothesis that P → Q
  apply hPQ
  -- apply the hypothesis that P → Q
  exact hP

-- If `a<b` and `b<c` then `a<c` -- that's called "transitivity of <"
-- theorem transitivity : (P → Q) → (Q → R) → (P → R) :=
-- begin
--   sorry
-- end
example : (P → Q → R) → (P → Q) → P → R := by
  intro hPQR
  intro hPQ
  intro hP
  apply hPQR
  assumption
  apply hPQ
  assumption

-- in Lean, the definition of ¬ P is `P → false` 
-- if P is true, ¬ P is false, and P → false is false
-- if P is false, then ¬ P is true, and P → false is true
example : P → ¬¬P := by
  intro hP
  change ¬P → False
  intro hnP
  change P → False at hnP 
  apply hnP
  assumption

example : ¬¬P → P := by finish

example : P → ¬¬P := by apply modus_ponens

-- and
example : P ∧ Q → P := by
  intro hPaQ
  cases' hPaQ with hP hQ
  assumption

theorem And.elim' : P ∧ Q → (P → Q → R) → R :=
  by
  intro hPaQ
  intro hPQR
  cases' hPaQ with hP hQ
  apply hPQR <;> assumption

theorem And.intro' : P → Q → P ∧ Q := by
  intro hP
  intro hQ
  constructor
  assumption
  assumption

