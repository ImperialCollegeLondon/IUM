import Mathbin.Tactic.Default

#align_import «2020».relations.equiv_partition2

namespace EquivPartition2

/-

data.equiv.basic  is the import which gives you the type `equiv X Y`, the type o
f
bijections from X to Y.

Here's the definition of equiv from that file.

structure equiv (α : Sort*) (β : Sort*) :=
(to_fun    : α → β)
(inv_fun   : β → α)
(left_inv  : left_inverse inv_fun to_fun)
(right_inv : right_inverse inv_fun to_fun)

To make a term of type `equiv α β` you have to supply a function α → β,
a function β → α, and proofs that both composites are the identity function.

Let's see how to create the bijection ℤ → ℤ sending x to -x.
-/
-- let's prove that x ↦ -x can be extended to
example : Equiv ℤ ℤ :=
  { toFun := fun x => -x
    -- this is data
    invFun := fun x => -x
    -- this is data
    left_inv :=
      by
      -- this is a proof
      change ∀ x : ℤ, - -x = x
      -- that's the question
      exact neg_neg
    -- note: I guessed what this function was called.
    -- If it had been called "lemma 12" I would not have been able to guess
    right_inv := neg_neg }

/- ./././Mathport/Syntax/Translate/Basic.lean:641:2: warning: expanding binder collection (A B «expr ∈ » ℱ) -/
-- another proof, this time in term mode
/-
Q1 Define the type of partitions of a type.
A partition of X is a set of subsets of X with the property that each subset
is non-empty and each element of X is in precisely one of the subsets.
NB : this is one of the harder questions here.
-/
structure Partition (X : Type _) where
  ℱ : Set (Set X)
  Disjoint : ∀ (A) (_ : A ∈ ℱ) (B) (_ : B ∈ ℱ), A ≠ B → A ∩ B = ∅
  cover : ∀ x : X, ∃ A ∈ ℱ, x ∈ A
  Nonempty : ∀ A ∈ ℱ, A ≠ ∅

/-
Equivalence relations are in core Lean -- we don't need any imports.
Here's an example: I'll prove that the "always true" relation on a set is
an equivalence relation.

-/
def AlwaysTrue (X : Type _) : X → X → Prop := fun a b => True

-- and now here's the proof that it's an equivalence relation.
theorem alwaysTrue_refl (X) : Reflexive (AlwaysTrue X) :=
  by
  intro x
  trivial

theorem alwaysTrue_symm (X) : Symmetric (AlwaysTrue X) :=
  by
  intro a b H
  trivial

theorem alwaysTrue_trans (X) : Transitive (AlwaysTrue X) :=
  by
  intro a b c Hab Hbc
  trivial

-- note pointy brackets to make a term of type "A ∧ B ∧ C"
theorem alwaysTrue_equiv (X) : Equivalence (AlwaysTrue X) :=
  ⟨alwaysTrue_refl X, alwaysTrue_symm X, alwaysTrue_trans X⟩

-- autocomplete made that proof really easy to type. It's really
-- lucky that I didn't call these lemmas lemma 12, lemma 13 and lemma 14.
-- if X is a type, then `setoid X` is is the type of equivalence relations on X.
-- I'll now make a term of type `setoid X` corresponding to that equivalence
-- relation above.
-- note squiggly brackets and commas at the end of each definition 
-- to make a structure
def alwaysTrueSetoid (X : Type _) : Setoid X
    where
  R := AlwaysTrue X
  iseqv := alwaysTrue_equiv X

/-
Q2 : If X is a type then `setoid X` is the type of equivalence relations on X,
and `partitions X` is the type of partitions of X. These two concepts are in
some sort of "canonical" bijection with each other (interesting exercise: make
this statement mathematically meaningful -- I know we all say it, but what
does it *mean*?).

Let's prove that these sets biject with each other by defining
a term of type equiv (setoid X) (partitions X)
-/
variable {X : Type _}

def f (S : Setoid X) : Partition X :=
  sorry

/-
Q3 : now define a map the other way
-/
def g (P : Partition X) : Setoid X :=
  sorry

/-
Q4 : now finally prove that the composite of maps in both directions
is the identity
-/
theorem FG_eq_id (P : Partition X) : f (g P) = P :=
  sorry

theorem GF_eq_id (S : Setoid X) : g (f S) = S :=
  sorry

/-
Q5 : now finally construct the term we seek.
-/
def partitionsBijectWithEquivalenceRelations : Equiv (Setoid X) (Partition X) :=
  sorry

end EquivPartition2

