
#align_import «2019».lectures.injsurj

open Function

example (X Y Z : Type) (f : X → Y) (g : Y → Z) (f_inj : Injective f) (g_inj : Injective g) :
    Injective (g ∘ f) := by
  unfold injective at *
  intro p q
  intro h
  apply f_inj
  apply g_inj
  exact h

example (X Y Z : Type) (f : X → Y) (g : Y → Z) (f_surj : Surjective f) (g_surj : Surjective g) :
    Surjective (g ∘ f) := by
  intro z
  cases' g_surj z with y hy
  cases' f_surj y with x hx
  exists x
  rw [← hy]
  rw [← hx]

