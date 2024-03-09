import Mathbin.Tactic.Default

#align_import «2020».problem_sheets.Part_II.sheet1_q2_solutions

namespace ProblemSheets2020PartIISheet2Q2Solutions

variable (x y : ℕ)

open Nat

theorem Q2a : 1 * x = x ∧ x = x * 1 := by
  constructor
  · induction' x with d hd
    rfl
    rw [mul_succ, hd]
  rw [mul_succ, MulZeroClass.mul_zero, zero_add]

-- Dr Lawn does not define z in her problem sheet.
-- Fortunately I can infer the type of z from the context.
variable (z : ℕ)

theorem Q2b : (x + y) * z = x * z + y * z :=
  by
  induction' z with d hd
  rfl
  rw [mul_succ, hd, mul_succ, mul_succ]
  ac_rfl

theorem Q2c : x * y * z = x * (y * z) :=
  by
  induction' z with d hd
  · rfl
  · rw [mul_succ, mul_succ, hd, mul_add]

-- Q3 def
def IsPred (x y : ℕ) :=
  x.succ = y

theorem Q3a : ¬∃ x : ℕ, IsPred x 0 := by
  intro h
  cases' h with x hx
  unfold is_pred at hx 
  apply succ_ne_zero x
  assumption

theorem Q3b : y ≠ 0 → ∃! x, IsPred x y := by
  intro hy
  cases y
  exfalso
  apply hy
  rfl
  clear hy
  use y
  constructor
  · dsimp only
    unfold is_pred
  intro z
  dsimp only [is_pred]
  exact succ_inj'.1

def aux : 0 < y → ∃ x, IsPred x y := by
  intro hy
  cases' Q3b _ (ne_of_lt hy).symm with x hx
  use x
  exact hx.1

-- definition of pred' is "choose a random d such that succ(d) = n"
noncomputable def pred' : ℕ+ → ℕ := fun nhn => Classical.choose (aux nhn nhn.2)

theorem pred'_def : ∀ np : ℕ+, IsPred (pred' np) np := fun nhn =>
  Classical.choose_spec (aux nhn nhn.2)

def succ' : ℕ → ℕ+ := fun n => ⟨n.succ, zero_lt_succ n⟩

noncomputable def q3c : ℕ+ ≃ ℕ where
  toFun := pred'
  invFun := succ'
  left_inv := by
    rintro np
    have h := pred'_def
    unfold succ'
    ext; dsimp
    unfold is_pred at h 
    rw [h]
  right_inv := by
    intro n
    unfold succ'
    have h := pred'_def
    unfold is_pred at h 
    rw [← succ_inj']
    rw [h]
    clear h
    rfl

end ProblemSheets2020PartIISheet2Q2Solutions

