import IUM.Nat.Definition

namespace MyNat

theorem succ_inj {a b : ℕ} (h : succ a = succ b) : a = b := MyNat.noConfusion h id

theorem zero_ne_succ (a : ℕ) : 0 ≠ succ a := MyNat.noConfusion

theorem zero_or_succ : ∀ x : ℕ, x = 0 ∨ ∃ n, x = succ n
  | 0 => by left; rfl
  | succ n => by right; use n

theorem eq_succ_of_ne_zero {x : ℕ} (hx : x ≠ 0) : ∃ n, x = succ n := by
  have := zero_or_succ x
  tauto
