import Mathbin.Tactic.Default

#align_import «2020».functions.bijection_game

-- experiments with bijections
-- experiments with bijections
/-

#check infinite

#print prefix infinite
#print infinite

#print int.infinite
#check infinite.of_injective

example : infinite ℕ := by apply_instance
example : infinite ℤ := by show_term {apply_instance}

#check rat.of_int

-/
/-

#check infinite

#print prefix infinite
#print infinite

#print int.infinite
#check infinite.of_injective

example : infinite ℕ := by apply_instance
example : infinite ℤ := by show_term {apply_instance}

#check rat.of_int

-/
example : Infinite ℚ :=
  Infinite.of_injective (coe : ℤ → ℚ)
    (by
      intro a b
      intro h
      exact (Rat.coe_int_inj a b).mp h)

namespace CountablyInfinite

example (a b : ℕ) : 2 * a = 2 * b → a = b := by
  intro h
  apply mul_right_injective₀ _ h
  norm_num

def boolTimesNat : Bool × ℕ ≃ ℕ
    where
  toFun bn := if bn.1 = true then bn.2 * 2 else bn.2 * 2 + 1
  invFun d := ⟨d % 2 = 0, d / 2⟩
  left_inv := by
    intro bn
    cases' bn with b n
    cases b
    -- TODO -- make snippet
    · suffices : ¬(1 + 2 * n) % 2 = 0 ∧ (1 + 2 * n) / 2 = n
      simpa [mul_comm, add_comm]
      have h : (1 + 2 * n) % 2 = 1
      simp
      constructor
      · simp
      · have h2 := Nat.mod_add_div (1 + 2 * n) 2
        have h3 : 2 * ((1 + 2 * n) / 2) = 2 * n → (1 + 2 * n) / 2 = n := fun h =>
          mul_right_injective₀ _ h
        simp_all; cc
    · simp
  right_inv := by
    intro n
    suffices : ite (n % 2 = 0) (n / 2 * 2) (n / 2 * 2 + 1) = n
    simpa
    split_ifs
    · have h2 := Nat.mod_add_div n 2
      rwa [h, zero_add, mul_comm] at h2 
    · have h2 := Nat.mod_add_div n 2
      rw [add_comm, mul_comm] at h2 
      convert h2
      rcases Nat.mod_two_eq_zero_or_one n with (h3 | h3)
      · contradiction
      · rw [h3]

-- example (X : Type) (h : X ≃ ℕ) : X ≃ X × bool := sorry
end CountablyInfinite

