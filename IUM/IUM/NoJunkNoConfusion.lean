import IUM.Definition

namespace MyNat

theorem succ_inj {a b : ℕ} (h : succ a = succ b) : a = b := MyNat.noConfusion h id

theorem zero_ne_succ (a : ℕ) : 0 ≠ succ a := MyNat.noConfusion

theorem zero_or_succ : ∀ x : ℕ, x = 0 ∨ ∃ n, x = succ n
  | 0 => by left; rfl
  | succ n => by right; use n
