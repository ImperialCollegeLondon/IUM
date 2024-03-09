/-  Math40001 : Introduction to university mathematics.

Problem Sheet 2, October 2020.

This is a Lean file. It can be read with the Lean theorem prover.

You can work on this file online via the link at
https://github.com/ImperialCollegeLondon/M40001_lean/blob/master/README.md


or you can install Lean and its maths library following the
instructions at
https://leanprover-community.github.io/get_started.html

and then just clone the project onto your own computer
with `leanproject get ImperialCollegeLondon/M40001_lean`.

There are advantages to installing Lean on your own computer
(for example it's faster), but it's more hassle than
just using it online.

In the below, delete "sorry" and replace it with some
tactics which prove the result.

-/
import Data.Real.Basic

#align_import «2020».problem_sheets.sheet2

-- need real numbers for Q5
-- need real numbers for Q5
namespace ProblemSheets2020Sheet2

-- Q1 prove that ∩ is symmetric
theorem question1 (α : Type) (X Y : Set α) : X ∩ Y = Y ∩ X := by sorry

-- question 2 defs
def a :=
  {x : ℝ | x ^ 2 < 3}

def b :=
  {x : ℝ | ∃ n : ℤ, x = n ∧ x ^ 2 < 3}

def c :=
  {x : ℝ | x ^ 3 < 3}

-- Change _true to _false and put a ¬ in front
-- of the goal if you think it's false.
-- e.g. if you think 2c is false then don't
-- try to prove it's true, try proving
-- lemma question2c_false : ¬ (A ⊆ C) := ...
-- Some of these are tricky for Lean beginners.
theorem question2a_true : (1 : ℝ) / 2 ∈ a ∩ b := by sorry

theorem question2b_true : (1 : ℝ) / 2 ∈ a ∪ b := by sorry

theorem question2c_true : a ⊆ c := by sorry

theorem question2d_true : b ⊆ c := by sorry

theorem question2e_true : c ⊆ a ∪ b := by sorry

theorem question2f_true : a ∩ b ∪ c = (a ∪ b) ∩ c := by sorry

-- Q3 set-up
variable (X Y : Type)

variable (P : X → Prop)

variable (Q : X → Prop)

variable (R : X → Y → Prop)

-- for Q3 you're going to have to change the right hand
-- side of the ↔ in the statement
-- of the lemma to the answer you think is correct.
theorem question3a : (¬∀ x : X, P x ∧ ¬Q x) ↔ True :=
  by-- change `true`!
  sorry

theorem question3b : (¬∃ x : X, ¬P x ∧ Q x) ↔ True :=
  by-- change `true`!
  sorry

theorem question3c : (¬∀ x : X, ∃ y : Y, R x y) ↔ True :=
  by-- change `true`!
  sorry

example (f : ℝ → ℝ) (x : ℝ) :
    (¬∀ ε : ℝ,
          ε > 0 →
            ∃ δ : ℝ,
              δ > 0 ∧
                ∀ y : ℝ,
                  abs (y - x) < δ →
                    abs (f y - f x) < ε) ↔-- change next line to what you think the answer is
      True :=
  by sorry

-- change _true to _false in 4a, 4b if you think the opposite is true
-- and stick a `¬` in front of it
theorem question4a_true : ∀ x : ℝ, ∃ y : ℝ, x + y = 2 := by sorry

theorem question4b_true : ∃ y : ℝ, ∀ x : ℝ, x + y = 2 := by sorry

-- similarly for Q5 -- change _true to _false and add in a negation if you 
-- want to prove that the proposition in the question is false.
theorem question5a_true : ∃ x ∈ (∅ : Set ℕ), 2 + 2 = 5 := by sorry

theorem question5b_true : ∀ x ∈ (∅ : Set ℕ), 2 + 2 = 5 := by sorry

end ProblemSheets2020Sheet2

