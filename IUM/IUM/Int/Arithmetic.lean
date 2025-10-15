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
