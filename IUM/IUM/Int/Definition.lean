import Verbose.Tactics.Lets

/-- The relation on `ℕ × ℕ` defined by, `(a, b)` ~ `(c, d)` if `a + d = b + c`, is an equivalence
relation. -/
theorem MyNat.equivalence : Equivalence (α := ℕ × ℕ) (fun (a, b) (c, d) ↦ a + d = b + c) where
  /- reflexivity -/
  refl := by
    intro (a, b)
    dsimp
    ring
  /- symmetry -/
  symm := by
    intro (a, b) (c, d) h
    dsimp at h ⊢
    calc c + b = b + c := by ring
      _ = a + d := by rw [h]
      _ = d + a := by ring
  /- transitivity -/
  trans := by
    intro (a, b) (c, d) (e, f) h1 h2
    dsimp at h1 h2 ⊢
    have :=
    calc
      (a + f) + d = a + d + f := by ring
      _ = b + c + f := by rw [h1]
      _ = b + (c + f) := by ring
      _ = b + (d + e) := by rw [h2]
      _ = (b + e) + d := by ring
    apply add_right_cancel at this
    exact this

instance : Setoid (ℕ × ℕ) := ⟨_, MyNat.equivalence⟩

/-- Our copy of the natural numbers called `MyInt`, with notation `ℤ`. -/
def MyInt := Quotient ⟨_, MyNat.equivalence⟩

@[inherit_doc]
notation (name := MyIntNotation) (priority := 1000000) "ℤ" => MyInt
-- Note: as long as we do not import `Mathlib.Data.Int.Notation` this is fine.

namespace MyInt

def i (n : ℕ) : ℤ := ⟦(n,0)⟧

theorem injective_i : Function.Injective i := by
  intro x y h1
  have h2 := Quotient.exact h1
  change x + 0 = 0 + y at h2
  convert h2 <;> ring

instance : OfNat ℤ 0 := ⟨i 0⟩
instance : OfNat ℤ 1 := ⟨i 1⟩
instance : OfNat ℤ 2 := ⟨i 2⟩
