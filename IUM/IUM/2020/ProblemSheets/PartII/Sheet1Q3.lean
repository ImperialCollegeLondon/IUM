import Mathbin.Tactic.Default

#align_import «2020».problem_sheets.Part_II.sheet1_q3

namespace ProblemSheets2020PartIISheet1Q3

variable (x y : ℕ)

open Nat

-- Q3 def
def IsPred (x y : ℕ) :=
  x.succ = y

theorem Q3a : ¬∃ x : ℕ, IsPred x 0 := by sorry

theorem Q3b : y ≠ 0 → ∃! x, IsPred x y := by sorry

def aux : 0 < y → ∃ x, IsPred x y := by sorry

-- definition of pred' is "choose a random d such that succ(d) = n"
noncomputable def pred' : ℕ+ → ℕ := fun nhn => Classical.choose (aux nhn nhn.2)

theorem pred'_def : ∀ np : ℕ+, IsPred (pred' np) np := fun nhn =>
  Classical.choose_spec (aux nhn nhn.2)

def succ' : ℕ → ℕ+ := fun n => ⟨n.succ, zero_lt_succ n⟩

noncomputable def q3c : ℕ+ ≃ ℕ where
  toFun := pred'
  invFun := succ'
  left_inv := by sorry
  right_inv := by sorry

end ProblemSheets2020PartIISheet1Q3

