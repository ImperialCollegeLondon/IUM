import Mathbin.Tactic.Default
import Data.Real.Basic

#align_import «2020».sets.lean_lecture

example : ∀ x : ℝ, ∃ y : ℝ, x + y > 0 := by
  intro x
  use 37 - x
  simp
  norm_num

-- example : ∃ y : ℝ, ∀ x : ℝ, x + y > 0 :=
-- begin
--   use 10000000000,
--   intro x,
--   -- stuck!
--   sorry
-- end
example : ¬∃ y : ℝ, ∀ x : ℝ, x + y > 0 := by
  push_neg
  intro y
  use-37 - y
  simp
  norm_num

variable (α : Type)

example : (α → Prop) ≃ Set α :=
  { toFun := fun P => {x : α | P x}
    invFun := fun X => fun a => a ∈ X
    left_inv := by
      intro P
      dsimp
      rfl
    right_inv := by
      intro X
      dsimp
      rfl }

