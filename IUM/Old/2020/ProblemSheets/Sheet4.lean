/-  Math40001 : Introduction to university mathematics.

Problem Sheet 4, October 2020.

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

#align_import «2020».problem_sheets.sheet4

-- the real numbers
-- the real numbers
namespace ProblemSheets2020Sheet4

/- Question 1. 

For each of the sets~$X$ and binary relations~$R$ below, figure out whether~$R$ is (a) reflexive, (b) symmetric, (c) antisymmetric, (d) transitive. 
  
  \begin{enumerate}
  \item Let $X$ be the set $\{1,2\}$ and define~$R$ like this: $R(1,1)$ is true, $R(1,2)$ is true, $R(2,1)$ is true and $R(2,2)$ is false. 
  \item Let~$X=\R$ and define $R(a,b)$ to be the proposition $a=-b$.
  \item Let~$X=\R$ and define $R(a,b)$ to be false for all real numbers~$a$ and~$b$.
  \item Let~$X$ be the empty set and define~$R$ to be the empty binary relation (we don't have to say what its value is on any pair $(a,b)$ because no such pairs exist).
  \end{enumerate}

-/
namespace Q1a

inductive X : Type
  | one : X
  | two : X

namespace X

def R : X → X → Prop
  | one, one => True
  | one, two => True
  | two, one => True
  | two, two => False

-- insert "¬" if you think it's not reflexive
theorem Q1a_refl : Reflexive R := by sorry

-- insert "¬" if you think it's not symmetric
theorem Q1a_symm : Symmetric R := by sorry

-- insert "¬" if you think it's not transitive
theorem Q1a_trans : Transitive R := by sorry

-- insert "¬" if you think it's not an equiv reln
theorem Q1a_equiv : Equivalence R := by sorry

end X

end Q1a

namespace Q1b

def R (a b : ℝ) : Prop :=
  a = -b

-- insert "¬" if you think it's not reflexive
theorem Q1b_refl : Reflexive R := by sorry

-- insert "¬" if you think it's not symmetric
theorem Q1b_symm : Symmetric R := by sorry

-- insert "¬" if you think it's not transitive
theorem Q1b_trans : Transitive R := by sorry

-- insert "¬" if you think it's not an equiv reln
theorem Q1b_equiv : Equivalence R := by sorry

end Q1b

namespace Q1c

def R (a b : ℝ) : Prop :=
  False

-- insert "¬" if you think it's not reflexive
theorem Q1c_refl : Reflexive R := by sorry

-- insert "¬" if you think it's not symmetric
theorem Q1c_symm : Symmetric R := by sorry

-- insert "¬" if you think it's not transitive
theorem Q1c_trans : Transitive R := by sorry

-- insert "¬" if you think it's not an equiv reln
theorem Q1c_equiv : Equivalence R := by sorry

end Q1c

namespace Q1d

def R (a b : Empty) : Prop := by cases a

-- i.e. "I'll define it in all cases -- oh look there are no cases"
-- insert "¬" if you think it's not reflexive
theorem Q1d_refl : Reflexive R := by sorry

-- insert "¬" if you think it's not symmetric
theorem Q1d_symm : Symmetric R := by sorry

-- insert "¬" if you think it's not transitive
theorem Q1d_trans : Transitive R := by sorry

-- insert "¬" if you think it's not an equiv reln
theorem Q1d_equiv : Equivalence R := by sorry

end Q1d

-- `set ℤ` is the type of subsets of the integers.
def q2a : PartialOrder (Set ℤ) where
  le A B := A ⊆ B
  le_refl := by sorry
  le_antisymm := by sorry
  le_trans := by sorry

-- insert ¬ at the beginning if you think it's wrong
theorem Q2b : IsTotal (Set ℤ) fun A B => A ⊆ B := by sorry

-- put ¬ in front if you think it's wrong
theorem Q3a : Symmetric fun a b : ℝ => a < b := by sorry

-- put ¬ in front if you think it's wrong
theorem Q3b : Symmetric fun a b : (∅ : Set ℝ) => a < b := by sorry

-- type in the proof in the question. Where do you get stuck?
theorem Q4 (X : Type) (R : X → X → Prop) (hs : Symmetric R) (ht : Transitive R) : Reflexive R := by
  sorry

open Function

def Pals {X Y Z : Type} (f : X → Y) (g : X → Z) :=
  ∃ h : Y → Z, Bijective h ∧ g = h ∘ f

theorem Q5 (X Y Z : Type) (f : X → Y) (g : X → Z) (hf : Surjective f) (hg : Surjective g) :
    Pals f g ↔ ∀ a b : X, f a = f b ↔ g a = g b := by sorry

end ProblemSheets2020Sheet4

