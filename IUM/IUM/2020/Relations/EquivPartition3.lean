import Logic.Equiv.Basic
import Data.Set.Basic

#align_import «2020».relations.equiv_partition3

namespace EquivPartition3

/- ./././Mathport/Syntax/Translate/Basic.lean:641:2: warning: expanding binder collection (c d «expr ∈ » C) -/
structure Partition (X : Type) where
  c : Set (Set X)
  Hnonempty : ∀ c ∈ C, c ≠ ∅
  Hcover : ∀ x, ∃ c ∈ C, x ∈ c
  Hunique : ∀ (c) (_ : c ∈ C) (d) (_ : d ∈ C), c ∩ d ≠ ∅ → c = d

def Partition.ext {X : Type} (P Q : Partition X) (H : P.c = Q.c) : P = Q :=
  by
  cases P; cases Q
  simpa using H

def equivalenceClass {X : Type} (R : X → X → Prop) (x : X) :=
  {y : X | R x y}

theorem mem_class {X : Type} {R : X → X → Prop} (HR : Equivalence R) (x : X) :
    x ∈ equivalenceClass R x := by
  cases' HR with HRR HR
  exact HRR x

example (X : Type) : { R : X → X → Prop // Equivalence R } ≃ Partition X :=
  { toFun := fun R =>
      { c := {S : Set X | ∃ x : X, S = equivalenceClass R x}
        Hnonempty := by
          intro c
          intro hc
          cases' hc with x hx
          rw [← Set.nonempty_iff_ne_empty]
          use x
          rw [hx]
          exact mem_class R.2 x
        Hcover := by
          intro x
          use equivalence_class R x
          exists _
          · exact mem_class R.2 x
          use x
        Hunique := by
          intro c hc d hd hcd
          rw [← Set.nonempty_iff_ne_empty] at hcd 
          cases' hcd with x hx
          cases' hc with a ha
          cases' hd with b hb
          cases' R with R HR
          cases' hx with hxc hxd
          rw [ha] at *
          rw [hb] at *
          change R a x at hxc 
          change R b x at hxd 
          rcases HR with ⟨HRR, HRS, HRT⟩
          apply Set.Subset.antisymm
          · intro y hy
            change R a y at hy 
            change R b y
            refine' HRT hxd _
            refine' HRT _ hy
            apply HRS
            assumption
          · intro y hy
            change R a y
            change R b y at hy 
            refine' HRT hxc _
            refine' HRT _ hy
            apply HRS
            assumption }
    invFun := fun P =>
      ⟨fun x y => ∃ c ∈ P.c, x ∈ c ∧ y ∈ c, by
        constructor
        · intro x
          cases' P.Hcover x with c hc
          cases' hc with hc hxc
          use c
          use hc
          constructor <;> assumption
        constructor
        · intro x y hxy
          cases' hxy with c hc
          cases' hc with hc1 hc2
          use c
          use hc1
          cases' hc2 with hx hy
          constructor <;> assumption
        · rintro x y z ⟨c, hc, hxc, hyc⟩ ⟨d, hd, hyd, hzd⟩
          use c
          use hc
          constructor
          exact hxc
          have hcd : c = d := by
            apply P.Hunique c hc d hd
            rw [← Set.nonempty_iff_ne_empty]
            use y
            constructor
            use hyc
            use hyd
          rw [hcd]
          use hzd⟩
    left_inv := by
      rintro ⟨R, HRR, HRS, HRT⟩
      ext x y
      suffices : (∃ c : Set X, (∃ x : X, c = equivalence_class R x) ∧ x ∈ c ∧ y ∈ c) ↔ R x y
      simpa
      constructor
      · rintro ⟨c, ⟨z, rfl⟩, ⟨hx, hy⟩⟩
        refine' HRT _ hy
        apply HRS
        exact hx
      · intro H
        use equivalence_class R x
        use x
        constructor
        exact HRR x
        exact H
    right_inv := by
      intro P
      dsimp
      cases' P with C _ _ _
      dsimp
      apply partition.ext
      dsimp
      -- dsimps everywhere
      ext c
      constructor
      · intro h
        dsimp at h 
        cases' h with x hx
        rw [hx]; clear hx
        rcases P_Hcover x with ⟨d, hd, hxd⟩
        convert hd
        -- not taught in NNG
        clear c
        ext y
        constructor
        · intro hy
          unfold equivalence_class at hy 
          dsimp at hy 
          rcases hy with ⟨e, he, hxe, hye⟩
          convert hye
          -- not taught
          refine' P_Hunique d hd e he _
          rw [← Set.nonempty_iff_ne_empty]
          use x
          constructor <;> assumption
        · intro hyd
          unfold equivalence_class; dsimp
          use d
          use hd
          constructor <;> assumption
      · intro hc
        dsimp
        have h := P_Hnonempty c hc
        rw [← Set.nonempty_iff_ne_empty] at h 
        cases' h with x hxc
        use x
        unfold equivalence_class
        ext y
        constructor
        · intro hyc
          dsimp
          use c
          use hc
          constructor <;> assumption
        · intro h
          dsimp at h 
          rcases h with ⟨d, hd, hxd, hyd⟩
          convert hyd
          apply P_Hunique c hc d hd
          rw [← Set.nonempty_iff_ne_empty]
          use x
          constructor <;> assumption }

end EquivPartition3

