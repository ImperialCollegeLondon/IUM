import Mathbin.Tactic.Default

#align_import «2020».problem_sheets.Part_II.sheet1_q1_solutions

namespace ProblemSheets2020PartIISheet1Q1Solutions

variable (x y : ℕ)

open Nat

theorem Q1a : x + y = y + x := by
  induction' y with d hd
  · rw [add_zero, zero_add]
  · rw [add_succ, succ_add, hd]

theorem Q1b : x + y = x → y = 0 := by
  intro h
  induction' x with d hd
  · convert h; rw [zero_add]
  · apply hd
    rw [succ_add] at h 
    rw [← succ_inj']
    assumption

theorem Q1c : x + y = 0 → x = 0 ∧ y = 0 := by
  intro h
  induction' y with d hd
  · constructor
    · exact h
    · rfl
  · rw [add_succ] at h 
    exfalso
    apply succ_ne_zero (x + d)
    assumption

theorem Q1d : x * y = y * x := by
  induction' y with d hd
  · rw [MulZeroClass.mul_zero, MulZeroClass.zero_mul]
  · rw [mul_succ, succ_mul, hd]

end ProblemSheets2020PartIISheet1Q1Solutions

