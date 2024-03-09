/-
What I present in M40001 is in some sense the mathematics
of true-false statements.
-/
import Mathbin.Tactic.Default

#align_import «2020».logic.logic_lecture_ad_lib

open Bool

/-
#print notation ∧
#print and
-- This is one idea of a proposition.
-- ff and tt are the only two terms of type `bool`
-- functions band, bor, bnot
#check ff ∧ tt
#eval band ff tt 
#eval tt
-/
example : ∀ p q r : Bool, (p && (q || r)) = (p && q || p && r) :=
  by
  intros
  cases p <;> cases q <;> cases r <;> rfl

#find Bool → Bool → Bool

-- afterwards change an and to an or,
-- note that it breaks.
/-
Very boring proofs.

But there is always something very weird about
the definition of →. Should it really be the case
that we say "p implies q" if p is completely
irrelevant to the proof of q? 
But there is actually a much more profound definition
of a Proposition. A Proposition in Lean is a type `P`, 
where `P : Prop`. 

You can make pretty much all of the material in
the pure part of Imperial's undergraduate degree
in Lean now, because of its maths library `mathlib`.
Many Imperial students have contributed to 
mathlib, but it's now getting harder for beginners
to help out.  


This definition looks intimidating
but it is not. A term `p : P` (that is,
a term `p` of type `P`)
is a proof of `P`. In this model of the idea of a
proposition, implication `P ⇒ Q` is a function,
which takes as input a proof of `P` and outputs a
proof of `Q`. In other words, a function
which takes as input a term of type `P` and outputs
a term of type `Q`. In other words, it's
a function `P → Q` between the types `P` and `Q`.

Important thing: any two proofs of `P` are equal.
If `p : P` and `q : P` then `p = q`. This model
of the word "proposition" cannot distinguish
between proofs. Internally a proof knows how
much work it was to construct though.
-/
/-
Let's do some constructive logic.
Let's play with the idea of `P → Q`.
-/
namespace Xena

variable (P Q R : Prop)

/-- The theorem that P ⇒ P -/
theorem id : P → P :=
  by
  -- `⊢ X` on the right means "you've got to prove X"
  -- so we've got to prove P → P
  -- assume that `P` is true. 
  -- call this hypotheis `hP`
  intro hP
  -- now we've got to prove `P`
  exact hP

-- we never mentioned `P`
-- we just talked about hypotheses
example : P → Q → P := by
  intro hP
  intro hQ
  exact hP

-- then remove bracket at the top
theorem modus_ponens : P → (P → Q) → Q := by
  intro hP
  intro hPQ
  apply hPQ; clear hPQ
  exact hP

-- `a<b` and `b<c` implies `a<c`
-- `a>b` and `b>c` implies `a>c`.
theorem trans : (P → Q) → (Q → R) → P → R :=
  by
  intro hPQ hQR hP
  apply hQR
  apply hPQ
  exact hP

theorem trans' : (P → Q) → (Q → R) → P → R := fun hPQ hQR hP => hQR <| hPQ hP

example : (P → Q → R) → (P → Q) → P → R := by
  intro hPQR
  intro hPQ
  intro hP
  apply hPQR
  exact hP
  exact hPQ hP

-- todo -- search for why I don't get multicoloured tada
example : (P → Q → R) → (P → Q) → P → R := by cc

-- "congruence closure"
-- `not P`, with notation `¬ P`, is 
-- *DEFINED TO MEAN* `P → false`
example : P → ¬¬P := by
  intro hP
  change ¬P → False
  intro hnP
  change P → False at hnP 
  apply hnP
  exact hP

theorem imp_not_not : P → ¬¬P := by
  change P → (P → False) → False
  apply modus_ponens

example : (P → Q) → ¬Q → ¬P :=
  by
  -- cc kills it
  intro hPQ
  intro hnQ
  intro hP
  change Q → False at hnQ 
  -- only change uses P,Q
  apply hnQ
  apply hPQ
  exact hP

#print axioms imp_not_not

theorem not_not : ¬¬P → P := by
  intro hnnP
  change (P → False) → False at hnnP 
  finish

#print axioms Classical.not_not

end Xena

