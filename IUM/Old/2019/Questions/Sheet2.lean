/-  Math40001 : Introduction to university mathematics.

Problem Sheet 2, October 2019.

This is a Lean file. It can be read with the Lean theorem prover.

You can work on this file online at 
https://tinyurl.com/Lean-M40001-Example-Sheet-2

or you can install Lean and its maths library following the
instructions at
https://github.com/leanprover-community/mathlib#installation

There are advantages to installing Lean on your own computer
(for example it's faster), but it's more hassle than
just using it online.

In the below, delete "sorry" and replace it with some
tactics which prove the result.

-/
import Data.Real.Basic

#align_import «2019».questions.sheet2

-- need real numbers for Q5
-- need real numbers for Q5
-- Q1 prove that ∩ is symmetric
-- Q1 prove that ∩ is symmetric
theorem question1 (Ω : Type) (X Y : Set Ω) : X ∩ Y = Y ∩ X := by sorry

-- Q2 we define the set U
def u : Set ℕ :=
  {1, 2, 3, 4, 5}

/- and then five of the questions still make sense
   in type theory, and the other three don't.
   What I'm saying is that b,f,g would continue to be
   wrong even if you changed the numbers around, because
   the questions do not even typecheck: U only contains
   numbers, and b, f, g are asking if a non-number is
   in U.

   For the remaining five questions, if you think they're
   false then change `_true` to `_false` and add a ¬ in front.
-/
theorem question2a_true : 1 ∈ u := by sorry

theorem question2c_true : {1} ⊆ u := by sorry

theorem question2d_true : {1, 2} ⊆ u := by sorry

theorem question2e_true : {1, 2, 1} ⊆ u := by sorry

theorem question2h_true : u ⊇ u := by sorry

-- question 3 defs
def a :=
  {x : ℝ | x ^ 2 < 3}

def b :=
  {x : ℝ | ∃ n : ℤ, x = n ∧ x ^ 2 < 3}

def c :=
  {x : ℝ | x ^ 3 < 3}

-- like Q2, change _true to _false and put a ¬ in front
-- of the goal if you think it's false.
theorem question3a_true : (1 : ℝ) / 2 ∈ a ∩ b := by sorry

theorem question3b_true : (1 : ℝ) / 2 ∈ a ∪ b := by sorry

theorem question3c_true : a ⊆ c := by sorry

theorem question3d_true : b ⊆ c := by sorry

theorem question3e_true : c ⊆ a ∪ b := by sorry

theorem question3f_true : a ∩ b ∪ c = (a ∪ b) ∩ c := by sorry

-- Q4 set-up
variable (X Y : Type)

variable (P : X → Prop)

variable (Q : X → Prop)

variable (R : X → Y → Prop)

-- for Q4 you're going to have to change the right hand
-- side of the ↔ in the statement
-- of the lemma to the answer you think is correct.
theorem question4a : (¬∀ x : X, P x ∧ ¬Q x) ↔ True :=
  by-- change `true`!
  sorry

theorem question4b : (¬∃ x : X, ¬P x ∧ Q x) ↔ True :=
  by-- change `true`!
  sorry

theorem question4c : (¬∀ x : X, ∃ y : Y, R x y) ↔ True :=
  by-- change `true`!
  sorry

example (f : ℝ → ℝ) (x : ℝ) :
    (¬∀ ε : ℝ,
          ε > 0 →
            ∃ δ : ℝ, δ > 0 → ∀ y : ℝ, abs (y - x) < δ → abs (f y - f x) < ε) ↔-- change next line
      True :=
  by sorry

-- change _true to _false in 5a, 5b if you think the opposite is true.
theorem question5a_true : ∀ x : ℝ, ∃ y : ℝ, x + y = 2 := by sorry

theorem question5b_true : ∃ y : ℝ, ∀ x : ℝ, x + y = 2 := by sorry

-- similarly for Q6 -- change _true to _false and add in a negation if you 
-- want to prove that the proposition in the question is false.
theorem question6a_true : ∃ x ∈ (∅ : Set ℕ), 2 + 2 = 5 := by sorry

theorem question6b_true : ∀ x ∈ (∅ : Set ℕ), 2 + 2 = 5 := by sorry

