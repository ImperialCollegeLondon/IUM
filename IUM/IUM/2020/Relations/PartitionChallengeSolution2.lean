import Mathbin.Tactic.Default

#align_import «2020».relations.partition_challenge_solution2

namespace PartitionChallengeSolution2

/-!

# Definition and basic API for partitions

-/


/- ./././Mathport/Syntax/Translate/Basic.lean:641:2: warning: expanding binder collection (X Y «expr ∈ » C) -/
-- Let α be a type. A *partition* on α is defined to
-- be the following data.
/-- The structure of a partition on a Type α. -/
@[ext]
structure Partition (α : Type) where
  -- A set C of subsets of α, called "blocks".
  c : Set (Set α)
  -- A hypothesis (a.k.a. a proof) that all the blocks are non-empty.
  Hnonempty : ∀ X ∈ C, (X : Set α).Nonempty
  -- A hypothesis that every term of type α is in one of the blocks.
  Hcover : ∀ a, ∃ X ∈ C, a ∈ X
  -- A hypothesis that two blocks with non-empty intersection are equal.
  Hdisjoint : ∀ (X) (_ : X ∈ C) (Y) (_ : Y ∈ C), (X ∩ Y : Set α).Nonempty → X = Y

namespace Partition

-- let α be a type, and fix a partition P on α. Let X and Y be subsets of α.
variable {α : Type} {P : Partition α} {X Y : Set α}

-- a more convenient way of putting it.
theorem Hdisjoint' (hX : X ∈ P.c) (hY : Y ∈ P.c) : (X ∩ Y).Nonempty → X = Y :=
  P.Hdisjoint X hX Y hY

-- another way
theorem Hdisjoint'' (hX : X ∈ P.c) (hY : Y ∈ P.c) {a : α} (haX : a ∈ X) (haY : a ∈ Y) : X = Y :=
  P.Hdisjoint _ hX _ hY ⟨a, haX, haY⟩

end Partition

section EquivalenceClasses

/-!

# Definition and basic API for equivalence classes 

We define equivalence classes and prove a few basic results about them.

-/


-- Notation and variables for this section:
-- let α be a type, and let R be an equivalence relation on R.
variable {α : Type} {R : α → α → Prop} (hR : Equivalence R)

-- Always assume R is an equivalence relation, even when we don't need it.
/-- The equivalence class of `x` is all the `y` such that `y` is related to `x`. -/
def cl (x : α) :=
  {y : α | R y x}

/-- Useful for rewriting -- `y` is in the equivalence class of `x` iff
`y` is related to `x`. True by definition. -/
theorem mem_cl_iff {x y : α} : x ∈ cl hR y ↔ R x y :=
  Iff.rfl

/-- x is in cl(x) -/
theorem mem_class_self (x : α) : x ∈ cl hR x :=
  by
  rcases hR with ⟨hrefl, hsymm, htrans⟩
  exact hrefl x

theorem class_sub {x y : α} : x ∈ cl hR y → cl hR x ⊆ cl hR y :=
  by
  rcases hR with ⟨hrefl, hsymm, htrans⟩
  intro hxy
  intro z
  intro hzx
  exact htrans hzx hxy

theorem class_eq {x y : α} : x ∈ cl hR y → cl hR x = cl hR y :=
  by
  intro hxy
  apply Set.Subset.antisymm
  apply class_sub hR hxy
  apply class_sub hR
  rcases hR with ⟨hrefl, hsymm, htrans⟩
  exact hsymm hxy

end EquivalenceClasses

/-!

# Statement of the theorem

-/


-- section
open Partition

-- There is a bijection between equivalence relations and partitions
example (α : Type) : { R : α → α → Prop // Equivalence R } ≃ Partition α :=
  { -- Let R be an equivalence relation.
    toFun := fun R =>
      { -- Let C be the set of equivalence classes for R.
        c := {B : Set α | ∃ x : α, B = cl R.2 x}
        -- I claim that C is a partition. We need to check three things.
        Hnonempty :=
          by
          -- If c is a block then c is nonempty.
          rintro c ⟨x, rfl⟩
          use x
          apply mem_class_self R.2
        Hcover := by
          intro x
          use cl R.2 x
          constructor
          · use x
          · apply mem_class_self
        Hdisjoint := by
          rintro c ⟨x, rfl⟩ d ⟨y, rfl⟩ ⟨z, hzx, hzy⟩
          cases' R with R hR
          erw [← class_eq hR hzx]
          erw [← class_eq hR hzy] }
    -- Conversely, say P is an partition.
    invFun := fun P =>
      -- Let's define a binary relation by x ~ y iff there's a block they're both in
      ⟨fun a b => ∀ X ∈ P.c, a ∈ X → b ∈ X,
        by
        -- I claim this is an equivalence relation.
        constructor
        · -- It's reflexive
          intro a C hC haC
          exact haC
        constructor
        · -- it's symmetric
          intro x y h C hC hyC
          rcases P.Hcover x with ⟨D, hD, hxD⟩
          convert hxD
          apply P.Hdisjoint _ hC _ hD
          use y, hyC
          exact h D hD hxD
        · -- it's transitive
          intro x y z hxy hyx C hC hxC
          apply hyx C hC
          apply hxy C hC
          exact hxC⟩
    -- If you start with the equivalence relation, and then make the partition
    -- and a new equivalence relation, you get back to where you started.
    left_inv := by
      rintro ⟨R, hR⟩
      simp
      ext a b
      rcases hR with ⟨hRr, hRs, hRt⟩
      constructor
      · intro f
        specialize f a (hRr a)
        exact hRs f
      · intro hab t hat
        refine' hRt _ hat
        exact hRs hab
    -- Similarly, if you start with the partition, and then make the
    -- equivalence relation, and then construct the corresponding partition 
    -- into equivalence classes, you have the same partition you started with.
    right_inv := by
      intro P
      ext W
      simp
      constructor
      · rintro ⟨a, rfl⟩
        rcases P.Hcover a with ⟨X, hX, haX⟩
        convert hX
        ext b
        rw [mem_cl_iff]
        constructor
        · intro h
          rcases P.Hcover b with ⟨Y, hY, hbY⟩
          specialize h Y hY hbY
          rwa [Hdisjoint'' hX hY haX h]
        · intro hbX Y hY hbY
          rwa [Hdisjoint'' hY hX hbY hbX]
      · intro hW
        cases' P.Hnonempty W hW with a haW
        use a
        ext b
        rw [mem_cl_iff]
        constructor
        · intro hbW
          intro X hX hbX
          rwa [Hdisjoint'' hX hW hbX hbW]
        · intro haX
          rcases P.Hcover b with ⟨X, hX, hbX⟩
          specialize haX X hX hbX
          rwa [Hdisjoint'' hW hX haW haX] }

end PartitionChallengeSolution2

