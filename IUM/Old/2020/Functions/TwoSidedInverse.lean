import Mathbin.Tactic.Default

#align_import «2020».functions.two_sided_inverse

/-! # Two-sided inverses

We define two-sided inverses, and prove that a function
is a bijection if and only if it has a two-sided inverse.

-/


-- let X and Y be types, and let f be a function.
variable {X Y : Type} (f : X → Y)

-- two-sided inverse
structure TwoSidedInverse (f : X → Y) where
  g : Y → X
  hX : ∀ x : X, g (f x) = x
  hY : ∀ y : Y, f (g y) = y

open Function

example : Bijective f ↔ Nonempty (TwoSidedInverse f) :=
  by
  constructor
  · intro hf
    cases' hf with hi hs
    choose g hg using hs
    let G : TwoSidedInverse f :=
      { g
        hX := by
          intro x
          apply hi
          rw [hg]
        hY := hg }
    use G
  · rintro ⟨g, hX, hY⟩
    constructor
    · intro a b hab
      apply_fun g at hab 
      rw [hX] at hab 
      rw [hX] at hab 
      assumption
    · intro y
      use g y
      apply hY

