import Mathbin.Tactic.Default
import Data.Setoid.Partition

#align_import «2020».relations.equiv_partition

--#check setoid.partition.rel_iso
--#check setoid.partition.rel_iso
open Setoid

variable (α : Type)

-- mathlib has this function already.
/-
def classes (r : setoid α) : set (set α) :=
{s | ∃ y, s = {x | r.rel x y}}
-/
--  set_option pp.notation false
example : { p : Set (Set α) // IsPartition p } ≃ Setoid α :=
  { toFun := fun pa =>
      { R := fun a b : α => ∀ X ∈ pa.1, a ∈ X → b ∈ X
        iseqv := by
          cases' pa with p hp
          dsimp only at *
          -- Need to check that the binary relation on α coming from 
          -- a partition p is reflexive, symmetric and transitive
          -- note that p is just the set of sets; hp is the proof
          -- that it's a partition.
          constructor
          · -- reflexive
            unfold Reflexive
            cc
          constructor
          · -- symmetric
            -- this needs thought
            -- rintros a b hab X (hX : X ∈ p) hbX,
            -- obtain ⟨Y, ⟨hYp, haY, -⟩, hY2⟩ := hp.2 a, simp at hY2,
            -- have hY3 : ∀ (Z : set α), Z ∈ p → a ∈ Z → Z = Y,
            rintro b c hbc X (hX : X ∈ p) hcX
            obtain ⟨Y, ⟨hYp, hcY, -⟩, hY2⟩ := hp.2 c; simp at hY2 
            have hpcY : ∀ Z : Set α, Z ∈ p → c ∈ Z → Z = Y
            simpa using hY2; clear hY2
            --specialize hab {x | r.rel x y}
            have hXY := hpcY X hX hcX
            obtain ⟨Z, ⟨hZp, hbZ, -⟩, hZ2⟩ := hp.2 b; simp at hZ2 
            have hcZ := hbc Z hZp hbZ
            have hZY := hpcY Z hZp hcZ
            rw [hXY, ← hZY]; exact hbZ
          · -- transitive
            intro b c d hbc hcd X hXp hbX
            apply hcd; exact hXp
            apply hbc <;> assumption }
    invFun := fun r =>
      ⟨classes r, by
        haveI : HasEquiv α := ⟨r.rel⟩
        constructor
        · -- empty set isn't an equiv class
          -- proof by contradiction
          intro h
          cases' h with a ha
          suffices : a ∈ (∅ : Set α)
          cases this
          rw [ha]
          simp only [Set.mem_setOf_eq]
        · intro a
          use{x : α | r.rel x a}
          dsimp only
          constructor
          · suffices : {x : α | r.rel x a} ∈ r.classes ∧ r.rel a a
            simpa
            constructor
            use a
            rfl
          · intro X
            rintro ⟨⟨c, rfl⟩, haX, -⟩
            ext b
            skip
            -- TODO must fix this notation
            change Setoid.r b c ↔ r.rel b a
            change r.rel a c at haX 
            constructor
            intro hbc
            apply r.iseqv.2.2
            -- these suck
            exact hbc
            apply r.iseqv.2.1
            exact haX
            -- need a ~ b <-> b ~ a
            intro hba
            apply r.iseqv.2.2; exact hba; exact haX⟩
    left_inv := by
      rintro ⟨p, hp⟩
      simp only
      ext X
      constructor
      · rintro ⟨b, rfl⟩
        obtain ⟨Y, ⟨hYp, hbY, -⟩, hY2⟩ := hp.2 b
        have hpb : ∀ y : Set α, y ∈ p → b ∈ y → y = Y
        simpa using hY2; clear hY2
        convert hYp
        ext c
        obtain ⟨Z, ⟨hZp, hcZ, -⟩, hY2⟩ := hp.2 c
        have hpc : ∀ y : Set α, y ∈ p → c ∈ y → y = Z
        simpa using hY2; clear hY2
        show (∀ X : Set α, X ∈ p → c ∈ X → b ∈ X) ↔ _
        constructor
        · intro hpcb
          specialize hpcb Z hZp hcZ
          specialize hpb Z hZp hpcb
          rw [← hpb]
          exact hcZ
        · intro hcY
          intro X hXp hcX
          have hXZ := hpc X hXp hcX
          have hYZ := hpc Y hYp hcY
          convert hbY
          cc
      · intro hXp
        have hX : X.nonempty
        have h := hp.1
        rw [Set.nonempty_iff_ne_empty]
        rintro rfl; contradiction
        cases' hX with b hbX
        use b
        ext c
        simp
        show c ∈ X ↔ ∀ X : Set α, X ∈ p → c ∈ X → b ∈ X
        constructor
        · intro hcX Y hYp hcY
          convert hbX
          obtain ⟨Z, ⟨hZp, hcZ, -⟩, hY2⟩ := hp.2 c
          have hpc : ∀ y : Set α, y ∈ p → c ∈ y → y = Z
          simpa using hY2; clear hY2
          have hYZ := hpc Y hYp hcY
          have hXZ := hpc X hXp hcX
          cc
        · intro hcb
          obtain ⟨Z, ⟨hZp, hcZ, -⟩, hY2⟩ := hp.2 c
          have hpc : ∀ y : Set α, y ∈ p → c ∈ y → y = Z
          simpa using hY2; clear hY2
          obtain ⟨Y, ⟨hYp, hbY, -⟩, hY2⟩ := hp.2 b
          have hpb : ∀ y : Set α, y ∈ p → b ∈ y → y = Y
          simpa using hY2; clear hY2
          have hZY := hpb Z hZp (hcb Z hZp hcZ)
          have hXY := hpb X hXp hbX
          cc
    right_inv := by
      rintro ⟨r, hrr, hrs, hrt⟩
      ext s
      simp only [Setoid.Rel]
      constructor
      · intro h
        specialize h {x : α | r x s} (by use s <;> rfl) (by apply hrr)
        apply hrs
        exact h
      · intro hrsb X
        rintro ⟨c, rfl⟩ h
        simp [Setoid.Rel] at h ⊢
        apply hrt; apply hrs; exact hrsb
        exact h }

