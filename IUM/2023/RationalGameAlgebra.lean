import Mathlib.Tactic

/-!

# The rationals

In this file we assume all standard facts about the integers, and then build
the rationals from scratch.

The strategy is to observe that every rationals can be written as `a / b`
for `a` and `b` integers witb `b ≠ 0`, so we define the "pre-rationals" to
be `ℤ × (ℤ - {0})`, the pairs `(a, b)` of integers. We define an equivalence
relation `≈` on `ℤ × (ℤ - {0})`, with the idea being that `(a, b) ≈ (c, d)`
if and only if `a / b = c / d`. This doesn't make sense yet, but the equivalent
equation `a * d = b * c` does. We prove that this is an equivalence relation,
and define the integers to be the quotient.

## The field structure on the rationals

We extend addition, subtraction and multiplication to the rationals, and also
define division. We then prove that the rationals are a field.

## TODO up to here
commutative ring. The proofs are all of
the form "reduce to a question about naturals, and then solve it using tactics
which prove theorems about naturals".

## The ordering on the integers

We prove that the integers are a total order, and also that the ordering
plays well with the ring structure.

-/

/-!

## The pre-rationals

-/

/-!

### Denominator API

-/
instance : Mul {x : ℤ // x ≠ 0} where
  mul a b := ⟨a.1 * b.1, mul_ne_zero a.2 b.2⟩

@[simp, norm_cast] lemma Int.ne_zero_coe_mul (a b : {x : ℤ // x ≠ 0}) :
    ((a * b : {x : ℤ // x ≠ 0}) : ℤ) = a * b := rfl

/-!

### Definition

-/

/-- A "pre-rational" is just a pair of integers, the second one non-zero. -/
abbrev MyPrerat := ℤ × {x : ℤ // x ≠ 0}

namespace MyPrerat

/-!

## The equivalence relation on the pre-rationals

-/

/-- The equivalence relation on pre-rationals, which we'll quotient out
by to get rationals. -/
def R (x y : MyPrerat) : Prop := x.1 * y.2 = x.2 * y.1

-- Lemma saying what definition of `R` is on ordered pairs
lemma R_def (a : ℤ) (b : {x : ℤ // x ≠ 0}) (c : ℤ) (d : {x : ℤ // x ≠ 0}) :
    R (a,b) (c,d) ↔ a * d = b * c := by rfl

-- `linarith` tactic can do all the calculations to prove it's an equiv reln
lemma R_refl : Reflexive R := by
  rintro ⟨a, b⟩
  simp only [R_def] at *
  linarith

lemma R_symm : Symmetric R := by
  rintro ⟨a, b⟩ ⟨c, d⟩ h
  simp only [R_def] at *
  linarith

lemma R_trans : Transitive R := by
  rintro ⟨a, b, hb⟩ ⟨c, d, hd⟩ ⟨e, f, hf⟩ h1 h2
  simp only [R_def] at *
  apply Int.eq_of_mul_eq_mul_right hd
  rw [mul_right_comm, h1, mul_assoc, h2, mul_right_comm, mul_assoc]

/-- Enable `≈` notation for `R` and ability to quotient by it  -/
instance R_equiv : Setoid MyPrerat where
  r := R
  iseqv := ⟨@R_refl, @R_symm, @R_trans⟩

-- Teach the definition of `≈` to the simplifier
@[simp] lemma equiv_def (a : ℤ) (b : {x : ℤ // x ≠ 0}) (c : ℤ) (d : {x : ℤ // x ≠ 0}) :
    (a, b) ≈ (c, d) ↔ a * d = b * c := R_def a b c d

-- Teach the definition of `Setoid.r` to the simplifier
@[simp] lemma equiv_def' (a : ℤ) (b : {x : ℤ // x ≠ 0}) (c : ℤ) (d : {x : ℤ // x ≠ 0}) :
    Setoid.r (a, b) (c, d) ↔ a * d = b * c := equiv_def a b c d

/-!

## The algebraic structure on the pre-rationals

-/

/-!

### Zero and one

We're not going to bother defining a 0 or a 1 on pre-rationals; they are an intermediate
object -- an implementation detail, which you shouldn't ever see in Lean code

-/

/-!

# Negation

-/


/-- Negation on pre-rationals. -/
def neg (ab : MyPrerat) : MyPrerat := (-ab.1, ab.2)

-- teach it to the simplifier
@[simp] lemma neg_def (a : ℤ) (b : {x : ℤ // x ≠ 0}) : neg (a, b) = (-a, b) := rfl


/-

## Addition

-/

/-- Addition on pre-rationals. -/
def add (ab cd : MyPrerat) : MyPrerat := (ab.1 * cd.2 + ab.2 * cd.1, ab.2 * cd.2)

-- teach it to the simplifier
@[simp] lemma add_def (a : ℤ) (b : {x : ℤ // x ≠ 0}) (c : ℤ) (d : {x : ℤ // x ≠ 0}) :
    add (a, b) (c, d) = (a * d + b * c, b * d) := rfl
/-

## Multiplication

-/

/-- Multiplication on pre-rationals. -/
def mul (ab cd : MyPrerat) : MyPrerat := (ab.1 * cd.1, ab.2 * cd.2)

-- teach it to the simplifier
@[simp] lemma mul_def (a : ℤ) (b : {x : ℤ // x ≠ 0}) (c : ℤ) (d : {x : ℤ // x ≠ 0}) :
  mul (a, b) (c, d) = (a * c, b * d) := rfl

/-

## Reciprocal

-/

/-- Reciprocal, or inverse, on pre-rationals. -/
def inv (ab : MyPrerat) : MyPrerat := if ha : ab.1 ≠ 0 then ⟨ab.2, ab.1, ha⟩ else ⟨0, 1, by simp⟩

-- teach it to the simplifier
@[simp] lemma inv_def {a : ℤ} (b : {x : ℤ // x ≠ 0}) (ha : a ≠ 0) :
    inv (a, b) = (b.1, ⟨a, ha⟩) := by
  unfold inv
  convert if_pos ha
  rfl -- surely this shouldn't happen **TODO**

lemma inv_def' (a : ℤ) (b : {x : ℤ // x ≠ 0}) :
  inv (a, b) = if ha : a ≠ 0 then ⟨b, a, ha⟩ else ⟨0, 1, by simp⟩ := rfl


end MyPrerat

open MyPrerat

/-!

## The rationals: definition and algebraic structure

-/

/-- Make the rationals as a quotient of prerationals. -/
abbrev MyRat := Quotient R_equiv

namespace MyRat

@[simp] lemma Quot_eq_Quotient (a : ℤ) (b : {x : ℤ // x ≠ 0}) :
    Quot.mk Setoid.r (a, b) = ⟦(a, b)⟧ := rfl

-- `0` notation (the equiv class of (0,0))
instance : Zero MyRat where zero := ⟦(0, ⟨1, one_ne_zero⟩)⟧

-- lemma stating definition of zero
lemma zero_def : (0 : MyRat) = ⟦(0, ⟨1, one_ne_zero⟩)⟧ := rfl

-- `1` notation (the equiv class of (1,0))
instance : One MyRat where one := ⟦(1, ⟨1, one_ne_zero⟩)⟧

-- lemma stating definition of one
lemma one_def : (1 : MyRat) = ⟦(1, ⟨1, one_ne_zero⟩)⟧ := rfl

/-- Negation on rationals. -/
def neg : MyRat → MyRat := Quotient.map MyPrerat.neg <| by
  -- to prove this is well-defined, we need to
  -- show some lemma or other
  rintro ⟨a, b⟩ ⟨c, d⟩ (h : a * d = b * c)
  simp [MyPrerat.neg]
  -- So prove this lemma
  linarith

-- unary `-` notation
instance : Neg MyRat where neg := neg

/-- Addition on integers. -/
def add : MyRat → MyRat → MyRat := Quotient.map₂ MyPrerat.add <| by
  -- to show this is well-defined, we need to
  -- show some lemma or other
  rintro ⟨a, b, hb⟩ ⟨c, d, hd⟩ (h1 : a * d = b * c)
         ⟨e, f, hf⟩ ⟨g, h, hh⟩ (h2 : e * h = f * g)
  simp [MyPrerat.add]
  -- So prove this lemma
  -- except that I have to work to do this
  -- *TODO* does `polyrith` do this?
  suffices (a * d) * (f * h) + (e * h) * (b * d) = (b * c) * (f * h) + (f * g) * (b * d) by
    linarith
  rw [h1, h2]

-- `+` notation
instance : Add MyRat where add := add

/-- Multiplication on integers. -/
def mul : MyRat → MyRat → MyRat  := Quotient.map₂ MyPrerat.mul <| by
  -- to show this is well-defined, we need to show some lemma or other
  rintro ⟨a, b, hb⟩ ⟨c, d, hd⟩ (h1 : a * d = b * c)
         ⟨e, f, hf⟩ ⟨g, h, hh⟩ (h2 : e * h = f * g)
  simp [MyPrerat.mul]
  -- so prove this lemma (which in this case is nonlinear)
  -- this is so polyrith **TODO**
  suffices (a * d) * (e * h) = (b * c) * (f * g) by
    linarith
  rw [h1, h2]

-- `*` notation
instance : Mul MyRat where mul := mul

lemma mul_def (a : ℤ) (b : {x : ℤ // x ≠ 0}) (c : ℤ) (d : {x : ℤ // x ≠ 0}) :
    (⟦(a, b)⟧ : MyRat) * ⟦(c, d)⟧ = ⟦(a * c, b * d)⟧ :=
  rfl

/-

## Inverse

-/
/-- reciprocal on nonzero rationals. -/
def inv : MyRat → MyRat := Quotient.map MyPrerat.inv <| by
  -- to prove this is well-defined, we need to
  -- show some lemma or other
  rintro ⟨a, b, hb⟩ ⟨c, d, hd⟩ (h : a * d = b * c)
  simp [MyPrerat.inv]
  -- So prove this lemma
  split
  · case inl ha =>
      subst ha -- a = 0
      rw [zero_mul, eq_comm, mul_eq_zero] at h
      rcases h with (rfl | rfl)
      · contradiction
      · -- so c = 0
        simp
  · case inr ha =>
      change a ≠ 0 at ha
      have hc : c ≠ 0 := by
        rintro rfl
        rw [mul_zero, mul_eq_zero] at h
        tauto
      split; contradiction
      exact h.symm

instance : Inv MyRat := ⟨inv⟩

lemma inv_def (a : ℤ) (b : {x : ℤ // x ≠ 0}) :
    (⟦(a, b)⟧ : MyRat)⁻¹ = ⟦MyPrerat.inv (a, b)⟧ := rfl

/-!

## Tactic hackery

Every single proof of every single ring axiom for the rationals is:
"replace all rationals with pairs of integers, turn the question into a question
about integers, and then get the `ring` tactic to prove it"

The problem is that we need three slightly different tactics depending on whether the
axiom mentions 1, 2 or 3 variables.

-/

macro "quot_proof₁" : tactic =>
  `(tactic|
  focus
    intro x
    refine Quot.induction_on x ?_
    rintro ⟨a, b⟩
    apply Quot.sound
    simp
    try ring)

macro "quot_proof₂" : tactic =>
  `(tactic|
  focus
    intro x y
    refine Quot.induction_on₂ x y ?_
    rintro ⟨a, b⟩ ⟨c, d⟩
    apply Quot.sound
    simp
    try ring)

macro "quot_proof₃" : tactic =>
  `(tactic|
  focus
    intro x y z
    refine Quot.induction_on₃ x y z ?_
    rintro ⟨a, b⟩ ⟨c, d⟩ ⟨e, f⟩
    apply Quot.sound
    simp
    try ring)

/-- Tactic for proving equality goals in rings defined as quotients. -/
macro "quot_proof" : tactic =>
  `(tactic|
  focus
    try quot_proof₁
    try quot_proof₂
    try quot_proof₃
  )

instance commRing : CommRing MyRat where
  add := (. + .)
  add_assoc := by quot_proof
  zero := 0
  zero_add := by quot_proof
  add_zero := by quot_proof
  add_comm := by quot_proof
  mul := (. * .)
  left_distrib := by quot_proof
  right_distrib := by quot_proof
  zero_mul := by quot_proof
  mul_zero := by quot_proof
  mul_assoc := by quot_proof
  one := 1
  one_mul := by quot_proof
  mul_one := by quot_proof
  neg := (- .)
  add_left_neg := by quot_proof
  mul_comm := by quot_proof

-- To make the rationals into a field we need to think a little more.

lemma zero_ne_one : (0 : MyRat) ≠ 1 := by
  simp [zero_def, one_def]

lemma mul_inv_cancel (a : MyRat) (ha : a ≠ 0) : a * a⁻¹ = 1 := by
  revert ha
  refine Quot.induction_on a ?_
  rintro ⟨b, c, hc⟩ h
  -- we know c ≠ 0
  change ⟦((b, ⟨c, hc⟩) : MyPrerat)⟧ ≠ 0 at h
  have hb : b ≠ 0 := by
    rintro rfl
    apply h
    apply Quotient.eq.2
    simp
  simp
  rw [inv_def, one_def]
  apply Quotient.eq.2
  simp [MyPrerat.mul]
  rw [MyPrerat.inv_def _ hb]
  simp [mul_comm]

instance field : Field MyRat where
  exists_pair_ne := ⟨0, 1, zero_ne_one⟩
  mul_inv_cancel := mul_inv_cancel
  inv_zero := rfl

/-!

## The natural map from the naturals to the rationals

-/

/-- The natural map from the naturals to the integers. -/
def i (n : ℕ) : MyRat := ⟦(n, ⟨1, by simp⟩)⟧

-- The natural map preserves 0
lemma i_zero : i 0 = 0 := rfl

-- The natural map preserves 1
lemma i_one : i 1 = 1 := rfl

-- The natural map preserves addition
lemma i_add (a b : ℕ) : i (a + b) = i a + i b := by
  apply Quot.sound
  simp

-- The natural map preserves multiplication
lemma i_mul (a b : ℕ) : i (a * b) = i a * i b := by
  apply Quot.sound
  simp

-- The natural map is injective
lemma i_injective (a b : ℕ) : i a = i b ↔ a = b := by
  constructor
  · intro h
    simp [i] at h
    assumption
  · rintro rfl
    rfl

/-!

## The natural map from the integers to the rationals

-/

/-- The natural map from the naturals to the integers. -/
def j (n : ℤ) : MyRat := ⟦(n, ⟨1, by simp⟩)⟧

-- The natural map preserves 0
lemma j_zero : j 0 = 0 := rfl

-- The natural map preserves 1
lemma j_one : j 1 = 1 := rfl

-- The natural map preserves addition
lemma j_add (a b : ℤ) : j (a + b) = j a + j b := by
  apply Quot.sound
  simp

-- The natural map preserves multiplication
lemma j_mul (a b : ℤ) : j (a * b) = j a * j b := by
  apply Quot.sound
  simp

-- The natural map is injective
lemma j_injective (a b : ℤ) : j a = j b ↔ a = b := by
  constructor
  · intro h
    simp [j] at h
    assumption
  · rintro rfl
    rfl

-- All the proofs were exactly the same as the natural number case.

-- Finally we check that the `i` and `j` commute with the natural
-- map `↑` from `ℕ` to `ℤ`:

lemma j_coe_eq_i : ∀ (n : ℕ), j (↑n : ℤ) = i n := by
  -- let `n` be arbitrary
  intro n
  -- turns it's true by definition
  rfl

-- We can now give a formula for `⟦(a, b)⟧` using `j a` and `j b`.

theorem Quotient.mk_def (a : ℤ) (b : {x : ℤ // x ≠ 0}) :
    ⟦(a, b)⟧ = j a * (j b)⁻¹ := by
  calc
  ⟦(a, b)⟧ = ⟦((a, ⟨1, by simp⟩) : MyPrerat)⟧ * ⟦(1, b)⟧ := by
    apply Quotient.sound
    simp [mul_comm]
  _        = j a * (⟦((b, ⟨1, by simp⟩) : MyPrerat)⟧)⁻¹ := by
    change j a * _ = _
    congr 1
    apply Quotient.sound
    rw [MyPrerat.inv_def _ b.2]

-- Now given a prerational, we never have to unfold it again,
-- because we have got the theorem giving the formula for
-- a general prerational, so we can just rewrite that instead.

end MyRat

/-!

Want more of this nonsense? See how the concept of order is developed
on the rational numbers in `RationalGemaOrder.lean`

-/
