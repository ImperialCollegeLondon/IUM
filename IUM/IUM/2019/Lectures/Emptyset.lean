
import Mathlib.Tactic

example (P : Prop) : ∀ x ∈ (∅ : Set ℕ), P := by
  intro x
  intro hx
  cases hx

example (P : Prop) : ∀ x ∈ (∅ : Set ℕ), P := by intro x hx; cases hx
