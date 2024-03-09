import Analysis.Convex.Basic

#align_import mathlib.analysis.convex.basic

open scoped BigOperators

open Finset

variable {𝕜 E ι : Type _} [OrderedRing 𝕜] [AddCommGroup E] [Module 𝕜 E] {m n : ℕ}

-- TODO: golf `affine_subspace.convex`
example (s : AffineSubspace 𝕜 E) : Convex 𝕜 (s : Set E) := fun x hx y hy a b ha hb hab =>
  calc
    a • x + b • y = b • (y - x) + x := Convex.combo_eq_smul_sub_add hab
    _ ∈ s := s.2 _ hy hx hx

