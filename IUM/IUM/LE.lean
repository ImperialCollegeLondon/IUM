import IUM.ConsequencesNoConfusion

namespace MyNat

def le (x y : ℕ) : Prop :=  ∃ n : ℕ, y = x + n

instance : LE ℕ := ⟨le⟩

-- ANCHOR: th_zero_le
Lemma zero_le
  "0 is no bigger than any other natural"
  Given: (x : ℕ)
  Assume:
  Conclusion: 0 ≤ x
Proof:
  Let's prove that ∃ n : ℕ, x = 0 + n
  Let's prove that x works
  We conclude by zero_add
QED
-- ANCHOR_END: th_zero_le

-- ANCHOR: th_le_refl
Lemma le_refl
  "A natural number is no bigger than itself"
  Given: (x : ℕ)
  Assume:
  Conclusion: x ≤ x
Proof:
  Let's prove that ∃ n : ℕ, x = x + n
  Let's prove that 0 works
  Apply definition of add
QED
-- ANCHOR_END: th_le_refl

-- ANCHOR: th_le_succ_self
Lemma le_succ_self
  "A natural number is no bigger than its successor"
  Given: (x : ℕ)
  Assume:
  Conclusion: x ≤ succ x
Proof:
  Let's prove that ∃ n : ℕ, succ x = x + n
  Let's prove that 1 works
  We conclude by succ_eq_add_one
QED
-- ANCHOR_END: th_le_succ_self

-- ANCHOR: th_le_zero
Lemma le_zero
  "Only 0 is no bigger than 0"
  Given: {x : ℕ}
  Assume: (hx : x ≤ 0)
  Conclusion: x = 0
Proof:
  Since ∃ n, 0 = x + n we get n such that hxn : 0 = x + n
  Since 0 = x + n we get hxn' : x + n = 0
  We conclude by add_right_eq_zero applied to hxn'
QED
-- ANCHOR_END: th_le_zero

Lemma le_trans
  "Transitivity of ≤"
  Given: {x y z : ℕ}
  Assume: (hxy : x ≤ y) (hyz : y ≤ z)
  Conclusion: x ≤ z
Proof:
  Since ∃ n, y = x + n we get a such that ha : y = x + a
  Since ∃ n, z = y + n we get b such that hb : z = y + b
  Let's prove that ∃ n, z = x + n
  Let's prove that a + b works
  Calc
    z = y + b       from hb
    _ = (x + a) + b from ha
    _ = x + (a + b) from add_assoc
QED

instance : Trans ((·: ℕ) ≤ ·) ((·: ℕ) ≤ ·) ((·: ℕ) ≤ ·) := ⟨le_trans⟩

-- ANCHOR: th_le_total
Lemma le_total
  "Totality of ≤"
  Given: (x y : ℕ)
  Assume:
  Conclusion: x ≤ y ∨ y ≤ x
Proof:
  Let's prove this by induction on y
  · Let's prove that 0 ≤ x
    We conclude by zero_le
  · Fix n : ℕ
    Assume hn : x ≤ n ∨ n ≤ x
    We discuss depending on whether x ≤ n or n ≤ x
    · Assume hxn : x ≤ n
      Let's prove that x ≤ succ n
      Calc
        x ≤ n      from hxn
        _ ≤ succ n from le_succ_self
    · Assume hnx : n ≤ x
      Since ∃ y, x = n + y we get y such that hxe : x = n + y
      By zero_or_succ applied to y we get he : y = 0 ∨ ∃ t, y = succ t
      We discuss depending on whether y = 0 or ∃ t, y = succ t
      · Assume hy : y = 0
        Let's prove that x ≤ succ n
        Calc
          x = n + y  from hxe
          _ = n + 0  from hy
          _ = n      by definition of add
          _ ≤ succ n from le_succ_self
      · Assume hy : ∃ t, y = succ t
        Since ∃ t, y = succ t we get t such that ht : y = succ t
        Let's prove that ∃ s, x = succ n + s
        Let's prove that t works
        Calc
          x = n + y        from hxe
          _ = n + succ t   from ht
          _ = succ (n + t) by definition of add
          _ = succ n + t   from succ_add
QED
-- ANCHOR_END: th_le_total
