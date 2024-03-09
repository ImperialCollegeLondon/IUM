import Mathlib.Tactic

/-!

# The integers

In this file we assume all standard facts about the naturals, and then build
the integers from scratch.

The strategy is to observe that every integer can be written as `a - b`
for `a` and `b` naturals, so we define the "pre-integers" to be `ℕ × ℕ`, the pairs
`(a, b)` of naturals. We define an equivalence relation `≈` on `ℕ × ℕ`, with the
idea being that `(a, b) ≈ (c, d)` if and only if `a - b = c - d`. This doesn't
make sense yet, but the equivalent equation `a + d = b + c` does. We prove
that this is an equivalence relation, and define the integers to be the quotient.

## The ring structure on the integers

We extend addition and multiplication to the integers, and also define subtraction.
We then prove that the integers are a commutative ring. The proofs are all of
the form "reduce to a question about naturals, and then solve it using tactics
which prove theorems about naturals".

## The ordering on the integers

We prove that the integers are a total order, and also that the ordering
plays well with the ring structure.

-/

/-!

## The pre-integers

-/

-- A "pre-integer" is just a pair of naturals.
abbrev MyPreint := ℕ × ℕ

namespace MyPreint

/-!

## The equivalence relation on the pre-integers

-/

/-- The equivalence relation on pre-integers, which we'll quotient out
by to get integers. -/
def R (x y : MyPreint) : Prop := x.1 + y.2 = x.2 + y.1

-- Lemma saying what definition of `R` is on ordered pairs
lemma R_def (a b c d : ℕ) : R (a,b) (c,d) ↔ a + d = b + c := by
  rfl

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
  rintro ⟨a, b⟩ ⟨c, d⟩ ⟨e, f⟩ h1 h2
  simp only [R_def] at *
  linarith

/-- Enable `≈` notation for `R` and ability to quotient by it  -/
instance R_equiv : Setoid MyPreint where
  r := R
  iseqv := ⟨@R_refl, @R_symm, @R_trans⟩

-- Teach the definition of `≈` to the simplifier
@[simp] lemma equiv_def (a b c d : ℕ) : (a, b) ≈ (c, d) ↔ a + d = b + c := R_def a b c d

-- Teach the definition of `Setoid.r` to the simplifier
@[simp] lemma equiv_def' (a b c d : ℕ) : Setoid.r (a, b) (c, d) ↔ a + d = b + c := equiv_def a b c d

/-!

## The algebraic structure on the pre-integers

-/

/-- Negation on pre-integers. -/
def neg (ab : MyPreint) : MyPreint := (ab.2, ab.1)

-- teach it to the simplifier
@[simp] lemma neg_def (a b : ℕ) : neg (a, b) = (b, a) := rfl

/-- Addition on pre-integers. -/
def add (ab cd : MyPreint) : MyPreint := (ab.1 + cd.1, ab.2 + cd.2)

-- teach it to the simplifier
@[simp] lemma add_def (a b c d : ℕ) : add (a, b) (c, d) = (a + c, b + d) := rfl

/-- Multiplication on pre-integers. -/
def mul (ab cd : MyPreint) : MyPreint := (ab.1 * cd.1 + ab.2 * cd.2, ab.1 * cd.2 + ab.2 * cd.1)

-- teach it to the simplifier
@[simp] lemma mul_def (a b c d : ℕ) : mul (a, b) (c, d) = (a * c + b * d, a * d + b * c) := rfl

end MyPreint

open MyPreint

/-!

## The integers: definition and algebraic structure

-/

/-- Make the integers as a quotient of preintegers. -/
abbrev MyInt := Quotient R_equiv

namespace MyInt

@[simp] lemma Quot_eq_Quotient (a b : ℕ) : Quot.mk Setoid.r (a, b) = ⟦(a, b)⟧ := rfl

-- `0` notation (the equiv class of (0,0))
instance : Zero MyInt where zero := ⟦(0, 0)⟧

-- lemma stating definition of zero
lemma zero_def : (0 : MyInt) = ⟦(0, 0)⟧ := rfl

-- `1` notation (the equiv class of (1,0))
instance : One MyInt where one := ⟦(1, 0)⟧

-- lemma stating definition of one
lemma one_def : (1 : MyInt) = ⟦(1, 0)⟧ := rfl

/-- Negation on integers. -/
def neg : MyInt → MyInt := Quotient.map MyPreint.neg <| by
  -- to prove this is well-defined, we need to
  -- show some lemma or other
  rintro ⟨a, b⟩ ⟨c, d⟩ (h : a + d = b + c)
  simp [MyPreint.neg]
  -- So prove this lemma
  linarith

-- unary `-` notation
instance : Neg MyInt where neg := neg

/-- Addition on integers. -/
def add : MyInt → MyInt → MyInt  := Quotient.map₂ MyPreint.add <| by
  -- to show this is well-defined, we need to
  -- show some lemma or other
  rintro ⟨a, b⟩ ⟨c, d⟩ (h1 : a + d = b + c)
         ⟨e, f⟩ ⟨g, h⟩ (h2 : e + h = f + g)
  simp [MyPreint.add]
  -- So prove this lemma
  linarith

-- `+` notation
instance : Add MyInt where add := add

/-- Multiplication on integers. -/
def mul : MyInt → MyInt → MyInt  := Quotient.map₂ MyPreint.mul <| by
  -- to show this is well-defined, we need to show some lemma or other
  rintro ⟨a, b⟩ ⟨c, d⟩ (h1 : a + d = b + c)
         ⟨e, f⟩ ⟨g, h⟩ (h2 : e + h = f + g)
  simp [MyPreint.mul]
  -- so prove this lemma (which in this case is nonlinear)
  nlinarith

-- `*` notation
instance : Mul MyInt where mul := mul

lemma mul_def (a b c d : ℕ) : (⟦(a, b)⟧ : MyInt) * ⟦(c, d)⟧ = ⟦(a * c + b * d, a * d + b * c)⟧ :=
  rfl

/-!

## Tactic hackery

Every single proof of every single ring axiom for the integers is:
"replace all integers with pairs of naturals, turn the question into a question
about naturals, and then get the `ring` tactic to prove it"

One slight problem is that we need three different tactics depending on whether the
axiom mentions 1, 2 or 3 variables. So we write three tactics and then one tactic
which does all three cases.

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

instance commRing : CommRing MyInt where
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

--#find Quotient.mk ?a ?b = Quotient.mk ?a ?c

lemma zero_ne_one : (0 : MyInt) ≠ 1 := by
  simp [zero_def, one_def]

/-!

## The map from the naturals to the integers

-/

/-- The natural map from the naturals to the integers. -/
def i (n : ℕ) : MyInt := ⟦(n, 0)⟧

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

## Linear order structure on the integers

-/

/-- We say `x ≤ y` if there's some natural `a` such that `y = x + a` -/
def le (x y : MyInt) : Prop := ∃ a : ℕ, y = x + i a

-- Notation `≤` for `le`
instance : LE MyInt where
  le := le

lemma le_refl (x : MyInt) : x ≤ x := by
  use 0 -- the idea in this proof
  revert x
  quot_proof₁

lemma le_trans (x y z : MyInt) (h1 : x ≤ y) (h2 : y ≤ z) : x ≤ z := by
  rcases h1 with ⟨p, rfl⟩
  rcases h2 with ⟨q, rfl⟩
  use p + q -- the idea in this proof
  revert x
  quot_proof₁

lemma le_antisymm (x y : MyInt) (hxy : x ≤ y) (hyx : y ≤ x) : x = y := by
  rcases hxy with ⟨p, rfl⟩
  rcases hyx with ⟨q, hq⟩
  rw [add_assoc, self_eq_add_right, ← i_add, ← i_zero, i_injective] at hq -- lots of ideas
  replace hq := Nat.eq_zero_of_add_eq_zero_right hq
  subst hq
  simp [i_zero]

lemma le_total (x y : MyInt) : x ≤ y ∨ y ≤ x := by
  refine Quot.induction_on₂ x y ?_
  rintro ⟨a, b⟩ ⟨c, d⟩
  rcases Nat.le_total (a + d) (b + c) with (h | h) -- idea
  · rw [le_iff_exists_add] at h
    rcases h with ⟨e, he⟩
    left
    use e
    apply Quot.sound
    simp
    linarith
  · rw [le_iff_exists_add] at h
    rcases h with ⟨e, he⟩
    right
    use e
    apply Quot.sound
    simp
    linarith

noncomputable instance linearOrder : LinearOrder MyInt where
  le := (. ≤ .)
  le_refl := le_refl
  le_trans := le_trans
  le_antisymm := le_antisymm
  le_total := le_total
  decidableLE := fun _ _ => Classical.propDecidable _

lemma zero_le_one : (0 : MyInt) ≤ 1 := by
  use 1
  rw [i_one]
  ring

/-

## Interaction between ordering and algebraic structure

-/

lemma add_le_add_left (x y : MyInt) (h : x ≤ y) (t : MyInt) : t + x ≤ t + y := by
  rcases h with ⟨n, rfl⟩
  use n
  ring

lemma aux_mul_lemma (a b c d : ℕ) (h : a * d + b * c = a * c + b * d) : a = b ∨ c = d := by
  induction' a with e he generalizing b
  · simp_all
    tauto
  · cases' b with f
    · simp_all
    · specialize he f
      simp
      apply he
      simp [Nat.succ_mul] at h
      linarith

lemma mul_pos (x y : MyInt) (ha : 0 < x) (hb : 0 < y) : 0 < x * y := by
  refine Ne.lt_of_le  ?_ ?_
  · replace ha := ha.ne
    replace hb := hb.ne
    revert ha hb
    refine Quot.induction_on₂ x y ?_
    rintro ⟨a, b⟩ ⟨c, d⟩ h1 h2
    simp_all [zero_def, mul_def]
    intro h
    cases aux_mul_lemma _ _ _ _ h <;> tauto
  · replace ha := ha.le
    replace hb := hb.le
    rcases ha with ⟨a, rfl⟩
    rcases hb with ⟨b, rfl⟩
    use a * b
    rw [i_mul]
    ring

    noncomputable instance : LinearOrderedCommRing MyInt :=
  { linearOrder, commRing with
    add_le_add_left := add_le_add_left
    exists_pair_ne := ⟨0, 1, zero_ne_one⟩
    zero_le_one := zero_le_one
    mul_pos := mul_pos
  }
