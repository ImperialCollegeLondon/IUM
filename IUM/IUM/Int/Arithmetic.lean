import Verbose.English.All
import IUM.Int.Definition

namespace MyInt

def prenegation : ℕ × ℕ → ℕ × ℕ := fun (a, b) ↦ (b, a)

-- ANCHOR: prenegation
Lemma prenegation_wd
  "Pre-negation is well-defined"
  Given: {a b c d : ℕ}
  Assume: (h : (a, b) ≈ (c, d))
  Conclusion: prenegation (a, b) ≈ prenegation (c, d)
Proof:
  We reformulate h as a + d = b + c
  Let's prove that b + c = a + d
  We conclude by h
QED
-- ANCHOR_END: prenegation

def neg : ℤ → ℤ := Quotient.lift _ (fun _ _ ↦ Quotient.sound ∘ prenegation_wd)

instance : Neg ℤ := ⟨neg⟩

def preaddition : ℕ × ℕ → ℕ × ℕ → ℕ × ℕ := fun (a, b) (c, d) ↦ (a + c, b + d)

-- ANCHOR: preaddition
Lemma preaddition_wd
  "Pre-addition is well-defined"
  Given: {a a' b b' c c' d d' : ℕ}
  Assume: (h1 : (a, b) ≈ (a', b')) (h2 : (c, d) ≈ (c', d'))
  Conclusion: preaddition (a, b) (c, d) ≈ preaddition (a', b') (c', d')
Proof:
  We reformulate h1 as a + b' = b + a'
  We reformulate h2 as c + d' = d + c'
  Let's prove that (a + c) + (b' + d') = (b + d) + (a' + c')
  Calc
    (a + c) + (b' + d') = (a + b') + (c + d') by computation
    _                   = (b + a') + (c + d') from h1
    _                   = (b + a') + (d + c') from h2
    _                   = (b + d) + (a' + c') by computation
QED
-- ANCHOR_END: preaddition

def add : ℤ → ℤ → ℤ :=
  Quotient.lift₂ _ (fun _ _ _ _ h1 h2 ↦ Quotient.sound <| preaddition_wd h1 h2)

instance : HAdd ℤ ℤ ℤ := ⟨add⟩

def sub (a b : ℤ) : ℤ := a + (-b)

instance : HSub ℤ ℤ ℤ := ⟨sub⟩

def premultiplication : ℕ × ℕ → ℕ × ℕ → ℕ × ℕ := fun (a, b) (c, d) ↦ (a * c + b * d, a * d + b * c)

-- ANCHOR: premultiplication
Lemma premultiplication_wd_1
  "Pre-multiplication is well-defined in the first variable"
  Given: {a a' b b' c d : ℕ}
  Assume: (h : (a, b) ≈ (a', b'))
  Conclusion:
    premultiplication (a, b) (c, d) ≈ premultiplication (a', b') (c, d)
Proof:
  We reformulate h as a + b' = b + a'
  Let's prove that (a * c + b * d) + (a' * d + b' * c)
    = (a * d + b * c) + (a' * c + b' * d)
  Calc
    (a * c + b * d) + (a' * d + b' * c)
      = (a + b') * c + (b + a') * d         by computation
    _ = (b + a') * c + (a + b') * d         from h
    _ = (a * d + b * c) + (a' * c + b' * d) by computation
QED

Lemma premultiplication_wd_2
  "Pre-multiplication is well-defined in the second variable"
  Given: {a b c c' d d' : ℕ}
  Assume: (h : (c, d) ≈ (c', d'))
  Conclusion:
    premultiplication (a, b) (c, d) ≈ premultiplication (a, b) (c', d')
Proof:
  We reformulate h as c + d' = d + c'
  Let's prove that (a * c + b * d) + (a * d' + b * c')
    = (a * d + b * c) + (a * c' + b * d')
  Calc
    (a * c + b * d) + (a * d' + b * c')
      = a * (c + d') + b * (d + c')         by computation
    _ = a * (d + c') + b * (c + d')         from h
    _ = (a * d + b * c) + (a * c' + b * d') by computation
QED
-- ANCHOR_END: premultiplication

lemma premultiplication_wd {a a' b b' c c' d d' : ℕ}
    (h1 : (a, b) ≈ (a', b')) (h2 : (c, d) ≈ (c', d')) :
    premultiplication (a, b) (c, d) ≈ premultiplication (a', b') (c', d') :=
  Trans.trans (premultiplication_wd_1 h1) (premultiplication_wd_2 h2)

def mul : ℤ → ℤ → ℤ :=
  Quotient.lift₂ _ (fun _ _ _ _ h1 h2 ↦ Quotient.sound <| premultiplication_wd h1 h2)

instance : HMul ℤ ℤ ℤ := ⟨mul⟩

macro "We represent" x:term "as (" a:ident "," b:ident ")" : tactic =>
  `(tactic | refine Quotient.inductionOn $x <| Prod.rec <| fun $a $b ↦ ?_)

macro "We lift to the relation on pairs" : tactic => `(tactic | refine Quotient.sound ?_)

Lemma add_comm
  "Addition on the integers is commutative"
  Given: (x y : ℤ)
  Assume:
  Conclusion: x + y = y + x
Proof:
  We represent x as (a, b)
  We represent y as (c, d)
  We lift to the relation on pairs
  Let's prove that (a + c, b + d) ≈ (c + a, d + b)
  We compute
QED

Lemma neg_add_cancel
  ""
  Given: (x : ℤ)
  Assume:
  Conclusion: (-x) + x = 0
Proof:
  We represent x as (a, b)
  We lift to the relation on pairs
  dsimp [preaddition, prenegation]
  Let's prove that (b + a, a + b) ≈ 0
  We compute
QED

Lemma neg_mul
  "Negation on the integers distributes"
  Given: (x y : ℤ)
  Assume:
  Conclusion: -(x * y) = (-x) * y
Proof:
  We represent x as (a, b)
  We represent y as (c, d)
  We lift to the relation on pairs
  Let's prove that
    (a * d + b * c, a * c + b * d) ≈ (b * c + a * d, b * d + a * c)
  We compute
QED

Lemma mul_comm
  "Multiplication on the integers is commutative"
  Given: (x y : ℤ)
  Assume:
  Conclusion: x * y = y * x
Proof:
  We represent x as (a, b)
  We represent y as (c, d)
  We lift to the relation on pairs
  Let's prove that
    (a * c + b * d, a * d + b * c) ≈ (c * a + d * b, c * b + d * a)
  We compute
QED

Lemma mul_assoc
  "Multiplication on the integers is associative"
  Given: (x y z : ℤ)
  Assume:
  Conclusion: x * y * z = x * (y * z)
Proof:
  We represent x as (a, b)
  We represent y as (c, d)
  We represent z as (e, f)
  We lift to the relation on pairs
  Let's prove that
    ((a * c + b * d) * e + (a * d + b * c) * f, (a * c + b * d) * f + (a * d + b * c) * e) ≈
    (a * (c * e + d * f) + b * (c * f + d * e), a * (c * f + d * e) + b * (c * e + d * f))
  We compute
QED

-- ANCHOR: th_distrib
Lemma mul_add
  "Multiplication on the integers is distributive"
  Given: (x y z : ℤ)
  Assume:
  Conclusion: x * (y + z) = x * y + x * z
Proof:
  We represent x as (a, b)
  We represent y as (c, d)
  We represent z as (e, f)
  We lift to the relation on pairs
  Let's prove that
    (a * (c + e) + b * (d + f), a * (d + f) + b * (c + e)) ≈
    ((a * c + b * d) + (a * e + b * f), (a * d + b * c) + (a * f + b * e))
  We compute
QED
-- ANCHOR_END: th_distrib

lemma add_i (a b : ℕ) : i (a + b) = i a + i b := by
  dsimp [i]
  apply Quotient.sound
  dsimp [preaddition]
  rfl

lemma mul_i (a b : ℕ) : i (a * b) = i a * i b := by
  dsimp [i]
  apply Quotient.sound
  dsimp [premultiplication]
  rw [zero_mul, zero_add]
  rfl

lemma exists_eq_or_eq_neg (x : ℤ) : (∃ n, x = i n) ∨ (∃ n, x = - i n) := by
  We represent x as (a, b)
  obtain h1 | h2 := le_total a b
  · obtain ⟨k, rfl⟩ : ∃ k, b = a + k := Nat.exists_eq_add_of_le h1
    right
    use k
    apply Quotient.sound
    show _ = _
    dsimp
  · obtain ⟨k, rfl⟩ : ∃ k, a = b + k := Nat.exists_eq_add_of_le h2
    left
    use k
    apply Quotient.sound
    show _ = _
    dsimp

lemma dvd_iff_dvd (a b : ℕ) : (∃ k, b = a * k) ↔ (∃ k, i b = i a * k) := by
  constructor
  · rintro ⟨k, rfl⟩
    use i k
    exact mul_i a k
  · intro ⟨k, hk⟩
    obtain ⟨k, rfl⟩ | ⟨k, rfl⟩ := exists_eq_or_eq_neg k
    · use k
      rw [← mul_i] at hk
      apply injective_i
      exact hk
    · have : i b + i a * i k = 0 := by
        rw [mul_comm, ← neg_mul] at hk
        rw [hk, mul_comm, neg_add_cancel]
      rw [← mul_i, ← add_i] at this
      change _ = i 0 at this
      apply injective_i at this
      obtain rfl : b = 0 := Nat.eq_zero_of_add_eq_zero_right this
      use 0
      ring
