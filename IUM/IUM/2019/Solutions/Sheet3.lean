import Data.Set.Image

#align_import «2019».solutions.sheet3

open Function Set

theorem question5 (X Y Z : Type) (f : X → Z) (g : Y → Z) (hf : Injective f) (hg : Injective g) :
    (∃ h : X → Y, Bijective h ∧ f = g ∘ h) ↔ Set.range f = Set.range g :=
  by
  constructor
  · rintro ⟨h, h1, h2⟩
    ext z
    constructor
    rintro ⟨x, hx⟩
    use h x
    convert hx
    rw [h2]
    rintro ⟨y, hy⟩
    cases' h1 with hinj hsurj
    cases' hsurj y with x hx
    use x
    rw [← hy]
    rw [← hx]
    rw [h2]
  · intro hfg
    have hx : ∀ x : X, ∃ y : Y, g y = f x
    intro x
    have hx : f x ∈ range f; use x
    rw [hfg] at hx 
    exact hx
    choose h hh using hx
    use h
    constructor
    constructor
    intro x1 x2 h12
    apply hf
    rw [← hh]
    rw [h12]
    exact hh x2
    intro y
    have hy : g y ∈ range g; use y
    rw [← hfg] at hy 
    cases' hy with x hx
    use x
    apply hg
    convert hx
    exact hh x
    ext x
    exact (hh x).symm

#check Eq.trans

