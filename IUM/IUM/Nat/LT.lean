import IUM.Nat.LE

namespace MyNat

def lt (a b : ℕ) : Prop := succ a ≤ b

instance : LT ℕ := ⟨lt⟩

-- problem sheet 4a
theorem lt_succ (x : ℕ) : x < succ x := le_refl _

-- problem sheet 4d(i)
theorem le_of_lt {x y : ℕ} (h : x < y) : x ≤ y :=
  le_trans (le_succ_self _) h

-- problem sheet 4d(ii)
theorem le_of_eq {x y : ℕ} (h : x = y) : x ≤ y :=
  h ▸ le_refl _

-- problem sheet 4e
theorem lt_or_eq_of_le {x y : ℕ} (h : x ≤ y) : x < y ∨ x = y := by
  obtain ⟨n, rfl⟩ := h
  obtain rfl | ⟨m, rfl⟩ := zero_or_succ n
  · right
    rfl
  · left
    use m
    rw [succ_add]
    rfl

-- problem sheet 4f(i)
theorem not_lt_self (x : ℕ) : ¬(x < x) := by
  rintro ⟨n, hn⟩
  have H :=
    calc
      succ n + x = x + succ n := add_comm ..
      _ = succ (x + n) := rfl
      _ = succ x + n := by rw [succ_add]
      _ = x := hn.symm
  exact zero_ne_succ _ (add_left_eq_self H).symm

-- problem sheet 4e
theorem not_lt_and_eq (x y : ℕ) : ¬ (x < y ∧ x = y) :=
  fun h ↦ not_lt_self y <| h.2 ▸ h.1
