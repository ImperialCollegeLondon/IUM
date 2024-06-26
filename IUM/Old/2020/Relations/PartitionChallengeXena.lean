import Mathbin.Tactic.Default

#align_import «2020».relations.partition_challenge_xena

namespace PartitionChallengeXena

/-!

# The partition challenge!

Prove that equivalence relations on α are the same as partitions of α.

Three sections:

1) partitions
2) equivalence classes
3) the challenge

## Overview

Say `α` is a type, and `R` is a binary relation on `α`. 
The following things are already in Lean:

reflexive R := ∀ (x : α), R x x
symmetric R := ∀ ⦃x y : α⦄, R x y → R y x
transitive R := ∀ ⦃x y z : α⦄, R x y → R y z → R x z

equivalence R := reflexive R ∧ symmetric R ∧ transitive R

In the file below, we will define partitions of `α` and "build some
interface" (i.e. prove some propositions). We will define
equivalence classes and do the same thing.
Finally, we will prove that there's a bijection between
equivalence relations on `α` and partitions of `α`.

-/


/- ./././Mathport/Syntax/Translate/Basic.lean:641:2: warning: expanding binder collection (X Y «expr ∈ » C) -/
/-

# 1) Partitions

We define a partition, and prove some easy lemmas.

-/
/- 

## Definition of a partition

Let `α` be a type. A *partition* on `α` is defined to be
the following data:

1) A set C of subsets of α, called "blocks".
2) A hypothesis (i.e. a proof!) that all the blocks are non-empty.
3) A hypothesis that every term of type α is in one of the blocks.
4) A hypothesis that two blocks with non-empty intersection are equal.
-/
/-- The structure of a partition on a Type α. -/
@[ext]
structure Partition (α : Type) where
  c : Set (Set α)
  Hnonempty : ∀ X ∈ C, (X : Set α).Nonempty
  Hcover : ∀ a : α, ∃ X ∈ C, a ∈ X
  Hdisjoint : ∀ (X) (_ : X ∈ C) (Y) (_ : Y ∈ C), (X ∩ Y : Set α).Nonempty → X = Y

/-

## Basic interface for partitions

-/
namespace Partition

-- let α be a type, and fix a partition P on α. Let X and Y be subsets of α.
variable {α : Type} {P : Partition α} {X Y : Set α}

/-- If X and Y are blocks, and a is in X and Y, then X = Y. -/
theorem eq_of_mem (hX : X ∈ P.c) (hY : Y ∈ P.c) {a : α} (haX : a ∈ X) (haY : a ∈ Y) : X = Y :=
  by
  have h := P.Hdisjoint X hX Y hY
  apply h
  use a
  constructor <;> assumption

/-- If a is in two blocks X and Y, and if b is in X,
  then b is in Y (as X=Y) -/
theorem mem_of_mem (hX : X ∈ P.c) (hY : Y ∈ P.c) {a b : α} (haX : a ∈ X) (haY : a ∈ Y)
    (hbX : b ∈ X) : b ∈ Y := by
  convert hbX
  exact (eq_of_mem hX hY haX haY).symm

/-- Every term of type `α` is in one of the blocks for a partition `P`. -/
theorem mem_block (a : α) : ∃ X : Set α, X ∈ P.c ∧ a ∈ X :=
  by
  rcases P.Hcover a with ⟨X, hXC, haX⟩
  use X
  constructor <;> assumption

end Partition

/-

# 2) Equivalence classes.

We define equivalence classes and prove a few basic results about them.

-/
section EquivalenceClasses

/-!

## Definition of equivalence classes 

-/


-- Notation and variables for the equivalence class section:
-- let α be a type, and let R be a binary relation on R.
variable {α : Type} (R : α → α → Prop)

/-- The equivalence class of `a` is the set of `b` related to `a`. -/
def cl (a : α) :=
  {b : α | R b a}

/-!

## Basic lemmas about equivalence classes

-/


/-- Useful for rewriting -- `b` is in the equivalence class of `a` iff
`b` is related to `a`. True by definition. -/
theorem cl_def {a b : α} : b ∈ cl R a ↔ R b a :=
  Iff.rfl

-- Assume now that R is an equivalence relation.
variable {R} (hR : Equivalence R)

/-- x is in cl_R(x) -/
theorem mem_cl_self (a : α) : a ∈ cl R a := by
  rw [cl_def]
  rcases hR with ⟨hrefl, hsymm, htrans⟩
  unfold Reflexive at hrefl 
  apply hrefl

/-- if a is in cl(b) then cl(a) ⊆ cl(b) -/
theorem cl_sub_cl_of_mem_cl {a b : α} : a ∈ cl R b → cl R a ⊆ cl R b :=
  by
  intro hab
  rw [Set.subset_def]
  intro x
  intro hxa
  rw [cl_def] at *
  rcases hR with ⟨hrefl, hsymm, htrans⟩
  exact htrans hxa hab

theorem cl_eq_cl_of_mem_cl {a b : α} : a ∈ cl R b → cl R a = cl R b :=
  by
  intro hab
  apply Set.Subset.antisymm
  · apply cl_sub_cl_of_mem_cl hR hab
  · apply cl_sub_cl_of_mem_cl hR
    rw [cl_def] at *
    rcases hR with ⟨hrefl, hsymm, htrans⟩
    apply hsymm
    exact hab

end EquivalenceClasses

/-!

# 3) The challenge!

Let `α` be a type (i.e. a collection of stucff).

There is a bijection between equivalence relations on `α` and
partitions of `α`.

We prove this by writing down constructions in each direction
and proving that the constructions are two-sided inverses of one another.
-/


-- section
open Partition

example (α : Type) : { R : α → α → Prop // Equivalence R } ≃ Partition α :=
  { -- We define constructions (functions!) in both directions and prove that
    -- one is a two-sided inverse of the other
    -- Here is the first construction, from equivalence
    -- relations to partitions.
    -- Let R be an equivalence relation.
    toFun := fun R =>
      { -- Let C be the set of equivalence classes for R.
        c := {B : Set α | ∃ x : α, B = cl R.1 x}
        -- I claim that C is a partition. We need to check the three
        -- hypotheses for a partition (`Hnonempty`, `Hcover` and `Hdisjoint`),
        -- so we need to supply three proofs.
        Hnonempty := by
          cases' R with R hR
          -- If X is an equivalence class then X is nonempty.
          show ∀ X : Set α, (∃ a : α, X = cl R a) → X.Nonempty
          sorry
        Hcover := by
          cases' R with R hR
          -- The equivalence classes cover α
          show ∀ a : α, ∃ (X : Set α) (H : ∃ b : α, X = cl R b), a ∈ X
          sorry
        Hdisjoint := by
          cases' R with R hR
          -- If two equivalence classes overlap, they are equal.
          show
            ∀ X : Set α,
              (∃ a : α, X = cl R a) → ∀ Y : Set α, (∃ b : α, Y = cl R b) → (X ∩ Y).Nonempty → X = Y
          sorry }
    -- Conversely, say P is an partition.
    invFun := fun P =>
      -- Let's define a binary relation `R` thus:
      --  `R a b` iff *every* block containing `a` also contains `b`.
      -- Because only one block contains a, this will work,
      -- and it turns out to be a nice way of thinking about it.
      ⟨fun a b => ∀ X ∈ P.c, a ∈ X → b ∈ X,
        by
        -- I claim this is an equivalence relation.
        constructor
        · -- It's reflexive
          show ∀ (a : α) (X : Set α), X ∈ P.C → a ∈ X → a ∈ X
          sorry
        constructor
        · -- it's symmetric
          show
            ∀ a b : α, (∀ X : Set α, X ∈ P.C → a ∈ X → b ∈ X) → ∀ X : Set α, X ∈ P.C → b ∈ X → a ∈ X
          sorry
        · -- it's transitive
          unfold Transitive
          show
            ∀ a b c : α,
              (∀ X : Set α, X ∈ P.C → a ∈ X → b ∈ X) →
                (∀ X : Set α, X ∈ P.C → b ∈ X → c ∈ X) → ∀ X : Set α, X ∈ P.C → a ∈ X → c ∈ X
          sorry⟩
    -- If you start with the equivalence relation, and then make the partition
    -- and a new equivalence relation, you get back to where you started.
    left_inv := by
      rintro ⟨R, hR⟩
      -- Tidying up the mess...
      suffices : (fun a b : α => ∀ c : α, a ∈ cl R c → b ∈ cl R c) = R
      simpa
      -- ... you have to prove two binary relations are equal.
      ext a b
      -- so you have to prove an if and only if.
      show (∀ c : α, a ∈ cl R c → b ∈ cl R c) ↔ R a b
      sorry
    -- Similarly, if you start with the partition, and then make the
    -- equivalence relation, and then construct the corresponding partition 
    -- into equivalence classes, you have the same partition you started with.
    right_inv :=
      by
      -- Let P be a partition
      intro P
      -- It suffices to prove that a subset X is in the original partition
      -- if and only if it's in the one made from the equivalence relation.
      ext X
      show (∃ a : α, X = cl _ a) ↔ X ∈ P.C
      dsimp only
      sorry }

/-
-- get these files with

leanproject get ImperialCollegeLondon/M40001_lean


leave this channel and go to a workgroup channel and try
folling in the sorrys.

I will come around to help.

-/
end PartitionChallengeXena

