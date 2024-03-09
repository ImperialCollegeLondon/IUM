import Mathbin.Tactic.Default

#align_import «2020».problem_sheets.Part_II_sheet1

variable (x y : ℕ)

open Nat

theorem Q1a : x + y = y + x := by sorry

theorem Q1b : x + y = x → y = 0 := by sorry

theorem Q1c : x + y = 0 → x = 0 ∧ y = 0 := by sorry

theorem Q1d : x * y = y * x := by sorry

theorem Q2a : 1 * x = x ∧ x = x * 1 := by sorry

variable (z : ℕ)

theorem Q2b : (x + y) * z = x * z + y * z := by sorry

theorem Q2c : x * y * z = x * (y * z) := by sorry

-- Q3 def
def IsPred (x y : ℕ) :=
  x.succ = y

theorem Q3a : ¬∃ x : ℕ, IsPred x 0 := by sorry

theorem Q3b : y ≠ 0 → ∃! x, IsPred x y := by sorry

