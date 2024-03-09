import Mathbin.Tactic.Default

#align_import «2020».relations.partition_challenge_official_solution

/-!

# The partition challenge!

Prove that equivalence relations on α are the same as partitions of α.

Three sections:

1) partitions
2) equivalence classes
3) the challenge

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
  Hcover : ∀ a, ∃ X ∈ C, a ∈ X
  Hdisjoint : ∀ (X) (_ : X ∈ C) (Y) (_ : Y ∈ C), (X ∩ Y : Set α).Nonempty → X = Y

-- docstrings
/-- The set of blocks. -/
add_decl_doc Partition.c

/-- Every element of a block is nonempty. -/
add_decl_doc Partition.Hnonempty

/-- The blocks cover the type they partition -/
add_decl_doc Partition.Hcover

/-- Two blocks which share an element are equal -/
add_decl_doc Partition.Hdisjoint

/-

## Basic interface for partitions

-/
namespace Partition

-- let α be a type, and fix a partition P on α. Let X and Y be subsets of α.
variable {α : Type} {P : Partition α} {X Y : Set α}

/-- If X and Y are blocks, and a is in X and Y, then X = Y. -/
theorem eq_of_mem (hX : X ∈ P.c) (hY : Y ∈ P.c) {a : α} (haX : a ∈ X) (haY : a ∈ Y) : X = Y :=
  -- Proof: follows immediately from the disjointness hypothesis.
      P.Hdisjoint
    _ hX _ hY ⟨a, haX, haY⟩

/-- If a is in two blocks X and Y, and if b is in X,
  then b is in Y (as X=Y) -/
theorem mem_of_mem (hX : X ∈ P.c) (hY : Y ∈ P.c) {a b : α} (haX : a ∈ X) (haY : a ∈ Y)
    (hbX : b ∈ X) : b ∈ Y :=
  by
  -- *great* place to teach convert here
  convert hbX
  apply eq_of_mem hY hX haY haX

theorem mem_block (a : α) : ∃ X : Set α, X ∈ P.c ∧ a ∈ X :=
  by
  -- new tactic
  rcases P.Hcover a with ⟨X, hX, haX⟩
  --  obtain ⟨X, hX, haX⟩ := P.Hcover a,
  use X
  constructor
  assumption
  exact haX

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
-- let α be a type, and let R be an equivalence relation on R.
variable {α : Type} (R : α → α → Prop)

/-- The equivalence class of `x` is the set of `y` related to `x`. -/
def cl (x : α) :=
  {y : α | R y x}

/-!

## Basic lemmas about equivalence classes

-/


/-- Useful for rewriting -- `y` is in the equivalence class of `x` iff
`y` is related to `x`. True by definition. -/
theorem cl_def {x y : α} : x ∈ cl R y ↔ R x y :=
  Iff.rfl

variable {R} (hR : Equivalence R)

/-- x is in cl(x) -/
theorem mem_cl_self (x : α) : x ∈ cl R x :=
  by
  rcases hR with ⟨hrefl, hsymm, htrans⟩
  -- rw on ↔
  rw [cl_def]
  -- understand how to use hrefl
  apply hrefl

theorem cl_sub_cl_of_mem_cl {x y : α} : x ∈ cl R y → cl R x ⊆ cl R y :=
  by
  rcases hR with ⟨hrefl, hsymm, htrans⟩
  intro h
  rw [cl_def] at h 
  -- new thing
  -- understand def of subset
  rw [Set.subset_def]
  intro z
  intro hzx
  rw [cl_def] at hzx ⊢
  unfold Transitive at htrans 
  apply htrans
  exact hzx
  exact h

theorem cl_eq_cl_of_mem_cl {x y : α} : x ∈ cl R y → cl R x = cl R y :=
  by
  intro hxy
  -- new function, find with library_search
  apply Set.Subset.antisymm
  apply cl_sub_cl_of_mem_cl hR
  assumption
  apply cl_sub_cl_of_mem_cl hR
  rcases hR with ⟨hrefl, hsymm, htrans⟩
  apply hsymm
  assumption

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
  { -- We define functions in both directions and prove that one is a two-sided
    -- inverse of the other
    -- Here is the first function (construction), from equivalence
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
          rintro _ ⟨a, rfl⟩
          --      unfold set.nonempty,
          use a
          rw [cl_def]
          rcases hR with ⟨hrefl, hsymm, htrans⟩
          apply hrefl
        Hcover := by
          cases' R with R hR
          -- The equivalence classes cover α
          show ∀ a : α, ∃ (X : Set α) (H : ∃ b : α, X = cl R b), a ∈ X
          intro a
          use cl R a
          constructor
          use a
          apply hR.1
        Hdisjoint := by
          cases' R with R hR
          -- If two equivalence classes overlap, they are equal.
          show
            ∀ X : Set α,
              (∃ a : α, X = cl R a) → ∀ Y : Set α, (∃ b : α, Y = cl _ b) → (X ∩ Y).Nonempty → X = Y
          rintro X ⟨a, rfl⟩ Y ⟨b, rfl⟩ ⟨c, hca, hcb⟩
          apply cl_eq_cl_of_mem_cl hR
          apply hR.2.2
          apply hR.2.1
          exact hca
          exact hcb }
    -- Conversely, say P is an partition.
    invFun := fun P =>
      -- Let's define a binary relation by x ~ y iff every block containing a,
      -- also contains b. Because only one block contains a, this will work,
      -- and it turns out to be a nice way of thinking about it.
      ⟨fun a b => ∀ X ∈ P.c, a ∈ X → b ∈ X,
        by
        -- I claim this is an equivalence relation.
        constructor
        · -- It's reflexive
          show ∀ (a : α) (X : Set α), X ∈ P.C → a ∈ X → a ∈ X
          intro a X hXC haX
          assumption
        constructor
        · -- it's symmetric
          show
            ∀ a b : α, (∀ X : Set α, X ∈ P.C → a ∈ X → b ∈ X) → ∀ X : Set α, X ∈ P.C → b ∈ X → a ∈ X
          intro a b h X hX hbX
          -- need to know something about how to use partitions.
          obtain ⟨Y, hY, haY⟩ := P.Hcover a
          specialize h Y hY haY
          exact mem_of_mem hY hX h hbX haY
        · -- it's transitive
          unfold Transitive
          show
            ∀ a b c : α,
              (∀ X : Set α, X ∈ P.C → a ∈ X → b ∈ X) →
                (∀ X : Set α, X ∈ P.C → b ∈ X → c ∈ X) → ∀ X : Set α, X ∈ P.C → a ∈ X → c ∈ X
          intro a b c hbX hcX X hX haX
          apply hcX; assumption
          apply hbX; assumption
          assumption⟩
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
      constructor
      · intro hab
        apply hR.2.1
        apply hab
        apply hR.1
      · intro hab c hac
        apply hR.2.2
        apply hR.2.1
        exact hab
        exact hac
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
      constructor
      · rintro ⟨a, rfl⟩
        obtain ⟨X, hX, haX⟩ := P.Hcover a
        convert hX
        ext b
        rw [cl_def]
        dsimp
        constructor
        · intro haY
          obtain ⟨Y, hY, hbY⟩ := P.Hcover b
          specialize haY Y hY hbY
          convert hbY
          exact eq_of_mem hX hY haX haY
        · intro hbX Y hY hbY
          apply mem_of_mem hX hY hbX hbY haX
      · intro hX
        rcases P.Hnonempty X hX with ⟨a, ha⟩
        use a
        ext b
        constructor
        · intro hbX
          rw [cl_def]
          dsimp
          intro Y hY hbY
          exact mem_of_mem hX hY hbX hbY ha
        · rw [cl_def]
          dsimp
          intro haY
          obtain ⟨Y, hY, hbY⟩ := P.Hcover b
          specialize haY Y hY hbY
          exact mem_of_mem hY hX haY ha hbY }

/-
-- get these files with
leanproject get ImperialCollegeLondon/M40001_lean

-/
