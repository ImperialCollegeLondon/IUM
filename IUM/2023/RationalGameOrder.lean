import IUM.«2023».RationalGameAlgebra

/-!

# The order on the rationals

Note: if you are just a *user* of the rationals, you don't ever need
to read this file. This file is for engineers only. The user-facing
API is just the fact that
`#synth LinearOrder MyRat` and
`#synth OrderedRing MyRat` both work.

We prove that the rationals are a total order, and also that the ordering
plays well with the ring structure.

## Nonnegativity

Let's practice by developing a theory of non-negativity.
Before we can start on non-negative rationals we will need
to develop an analogous theory in the "plumbing", i.e.
working with prerationals again.

Homework: There is a completely different way of defining non-negativity:
you could say that a rational was non-negative if it was the sum
of a finite number of squares of rationals. This means that you don't
have to unfold down to the prerational stage -- you can define the order
on the rationals using only the algebra of the rationals. However to
prove that these concepts are the same, you're going to have to show
that every natural number is the sum of some finite number of squares
(with the optimal number being four), and this is a delicate induction.

## Nonnegativity on the pre-rationals

-/

namespace MyPrerat

/-- This stuff will only be used to do nonnegativity on the rationals
so it should be regarded as an implementation detail (as should all
of "prerational theory"). -/
def IsNonneg (ab : MyPrerat) : Prop := ab.1 ≥ 0 ∧ ab.2.1 > 0

-- This doesn't mean "a/b >= 0", but it implies it, and this is
-- all we care about

lemma IsNonneg_def (a : ℤ) (b : {x : ℤ // x ≠ 0}) :
    IsNonneg (a, b) ↔ a ≥ 0 ∧ b.1 > 0 := by
  simp [IsNonneg]

/-!

We don't even need any API for this, we just needed a definition
so that we could define

### Relationship with the equivalence relation

There seems to be no relationship between non-negativity and
the equivalence relation.

You can have two inequavalent prerationals which are both nonnegative,
and you can have two equivalent prerationals where one is nonnegative
and the other is not.

-/

/-!

## Relationship with the algebraic structure.

Here we could prove `IsNonneg 0` and `IsNonneg 1` (except we didn't
bother to even define these things,

We could then prove all of these.

`IsNonneg x → IsNonneg -x → x = 0`
`IsNonneg x → IsNonneg y → IsNonneg (x + y)`
`IsNonneg x → IsNonneg y → IsNonneg (x * y)`
`IsNonneg x → IsNonneg x⁻¹`

-/

end MyPrerat

open MyPrerat

namespace MyRat

/-

## Nonnegativitiy on the rationals

-/
-- this definition is somehow bad as it asks for proofs of b≠0 and b>0
def IsNonneg (x : MyRat) : Prop :=
  ∃ (a b : ℤ) (ha : 0 ≤ a) (hb : 0 < b), x = ⟦(a, ⟨b, hb.ne'⟩)⟧

/-

### Relationship with 0 and 1

-/

@[simp]
lemma zero_nonneg : IsNonneg 0 := by
  use 0, 1
  simp [zero_def]

@[simp]
lemma one_nonneg : IsNonneg 1 := by
  use 1, 1
  simp [one_def]

/-

## Relationship with neg

-/

lemma nonneg_neg {x : MyRat} (h : IsNonneg x) (h' : IsNonneg (-x)) :
    x = 0 := by
  -- manually reduce it to a question about integers
  rcases h with ⟨a, b, ha, hb, rfl⟩
  rcases h' with ⟨c, d, hc, hd, h⟩
  -- currently a question about equalities of equivalence classes following from other equalities
  -- Turn all these hypotheses and conclusions into concrete statements about integers
  apply Quotient.eq.2
  apply Quotient.eq.1 at h
  -- They're unreadable so let the simplifier tidy them up
  simp_all
  -- and now it's a really boring puzzle about integers. Here it is:
  /-
  a b : ℤ
  c d : ℤ
  ha : 0 ≤ a
  hb : 0 < b
  hc : 0 ≤ c
  hd : 0 < d
  h : -(a * d) = b * c
  ⊢ a = 0
  -/
  -- We just blast it with a nonlinear inequality tactic
  nlinarith

-- this one is also useful
lemma nonneg_neg_of_not_nonneg {x : MyRat} : ¬ IsNonneg x → IsNonneg (-x) := by
  refine Quot.induction_on x ?_
  clear x
  rintro ⟨a, ⟨b, hb⟩⟩ h
  simp [IsNonneg] at *
  -- This is as you can imagine a big case bash depending on the signs of a and b.
  -- The question is to build a nonnegative prerational that maps onto -(a/b)
  -- given that a/b is not nonnegative. We argue by cases on whether a is nonnegative.
  by_cases ha : 0 ≤ a
  -- In  a>=0 then the prerational we're going to use is a/(-b).
  · use a, ha, -b
    -- We know x is not nonnegative. So if a>=0 then b had better be <0
    have foo : 0 < -b := by
      -- because if b>=0 then x=a/b is a nonnegative prerational, a contradiction.
      by_contra!
      exact h a b (show 0 < b by omega) ha <| mul_comm _ _
    clear h -- don't need hypothesis that x is not nonnegative any more.
    -- A machine can do the rest.
    use foo
    apply Quotient.eq.2 -- remaining goal of the form ⟦(p,q)⟧=⟦(r,s)⟧ so turn it into a question
                        -- about integers being equivalent
    simp [mul_comm] -- the simplifier reduces this random question to `mul_comm` on `ℤ`
  · push_neg at ha
    use -a, (by omega)
    have foo : ¬ 0 < -b := by
      -- foo true because other wise you can use h to get a contradiction
      intro hb
      exact h (-a) (-b) hb (by omega) (by ring)
    use b, (by omega)
    apply Quotient.eq.2
    simp [mul_comm]
/-

## Relationship with addition

-/

lemma isNonneg_add_isNonneg {x y : MyRat} (hx : IsNonneg x) (hy : IsNonneg y) :
    IsNonneg (x + y) := by
  rcases hx with ⟨a, b, ha, hb, rfl⟩
  rcases hy with ⟨c, d, hc, hd, rfl⟩
  use a * d + b * c, b * d, (by nlinarith), (by nlinarith)
  apply Quotient.eq.2
  simp
  ring

/-

## Relationship with multiplication

-/

-- github copilot wrote the first proof I had of this
lemma isNonneg_mul_isNonneg {x y : MyRat} (hx : IsNonneg x) (hy : IsNonneg y) :
    IsNonneg (x * y) := by
  rcases hx with ⟨a, b, ha, hb, rfl⟩
  rcases hy with ⟨c, d, hc, hd, rfl⟩
  use a * c, b * d, by nlinarith, by nlinarith
  apply Quotient.eq.2
  simp
  ring

/-

## Relationship with inverse

-/

lemma isNonneg_inv_isNonneg {x : MyRat} (hx : IsNonneg x) :
    IsNonneg x⁻¹ := by
  rcases hx with ⟨a, b, (ha : 0 ≤ a), (hb2 : 0 < b), rfl⟩
  rcases eq_or_ne a 0 with (rfl | ha2)
  · use 0, 1, by simp
    simp [IsNonneg, IsNonneg_def]
    rfl
  · use b, a, by omega, by omega
    apply Quotient.eq.2
    simp [MyPrerat.inv, ha2, mul_comm]

/-!

## The linear order on the rationals

I think that's it for non-negativity on the rationals. Let's see
if we can use those theorems about nonnegativity to prove that
the raionals are a linear order.

-/

/-- Our definition of x ≤ y on the rationals. -/
def le (x y : MyRat) : Prop := IsNonneg (y - x)

instance : LE MyRat where
  le := le

lemma le_def (x y : MyRat) : x ≤ y ↔ IsNonneg (y - x) := by
  rfl

lemma zero_le_iff_IsNonneg (x : MyRat) : 0 ≤ x ↔ IsNonneg x := by
  simp [le_def]
/-!

We now develop some basic theory of `≤` on the rationals.
Let's warm up with 0 ≤ 1.

-/

lemma zero_le_one : (0 : MyRat) ≤ 1 := by
  simp [le_def]

/-!

There's no point proving 0 ≤ 0 and 1 ≤ 1, we may as well prove reflexivity
in general.

-/

lemma le_refl (x : MyRat) : x ≤ x := by
  simp [le_def]

/-!

Next is transitivitiy

-/

lemma le_trans (x y z : MyRat) (h1 : x ≤ y) (h2 : y ≤ z) : x ≤ z := by
  simp [le_def] at *
  convert isNonneg_add_isNonneg h1 h2 using 1
  ring

/-!

Next is antisymmetry

-/

lemma le_antisymm (x y : MyRat) (hxy : x ≤ y) (hyx : y ≤ x) : x = y := by
  simp [le_def] at *
  have foo : IsNonneg (-(y - x)) := by
    convert hyx using 1
    ring
  have := nonneg_neg hxy foo
  linear_combination -(1 * this)

lemma add_le_add_left (x y : MyRat) (h : x ≤ y) (t : MyRat) : t + x ≤ t + y := by
  simp_all [le_def]

lemma mul_nonneg (x y : MyRat) (hx : 0 ≤ x) (hy : 0 ≤ y) : 0 ≤ x * y := by
  simp_all [le_def]
  convert isNonneg_mul_isNonneg hx hy using 1

instance : OrderedRing MyRat where
  le := (. ≤ .)
  le_refl := le_refl
  le_trans := le_trans
  le_antisymm := le_antisymm
  add_le_add_left := add_le_add_left
  zero_le_one := zero_le_one
  mul_nonneg := mul_nonneg

/-!

The interplay between the ordering and the natural maps from
the naturals and integers to the rationals.

-/

-- let's do `j` first, then we can use it for `i`

/-- The natural map from the integers to the rationals
preserves and reflects `≤`. -/
lemma j_le (p q : ℤ) : j p ≤ j q ↔ p ≤ q := by
  change IsNonneg _ ↔ _
  refine ⟨?_, ?_⟩
  · rintro ⟨a, b, (ha : 0 ≤ a), (hb : 0 < b), h⟩
    apply Quotient.eq.1 at h
    simp at h
    nlinarith
  · intro h
    use q - p, 1, by omega, by omega
    apply Quotient.eq.2
    simp
    ring

/-- The natural map from the naturals to the rationals preserves
and reflects `≤`. -/
lemma i_le (a b : ℕ) : i a ≤ i b ↔ a ≤ b := by
  change IsNonneg _ ↔ _
  simp [le_def, IsNonneg, IsNonneg_def]
  constructor
  · rintro ⟨c, hc, d, hd, h⟩
    simp [MyRat.Quotient.mk_def ] at h
    suffices (a : ℤ) ≤ (b : ℤ) from by
      exact_mod_cast this
    change j b - j a = _ at h
    generalize hb : (b : ℤ) = e
    rw [hb] at h
    generalize ha : (a : ℤ) = f
    rw [ha] at h
    clear! a b
    have foo : j f ≤ j e := by
      rw [le_def]
      rw [h]
      apply isNonneg_mul_isNonneg
      · use c, 1
        simp [IsNonneg, IsNonneg_def]
        aesop
      · refine ⟨1, d, by simp, hd, ?_⟩
        apply Quotient.eq.2
        rw [MyPrerat.inv_def]
    · clear! c d
      -- this should be done elsewhere
      rwa [j_le] at foo
  · intro h
    rw [le_iff_exists_add] at h
    rcases h with ⟨c, rfl⟩
    use c, by simp, 1, by simp
    change i (a + c) - i a = i c
    rw [sub_eq_iff_eq_add, i_add, add_comm]

/-!

## Linear order structure on the rationals

-/

def le_total (a b : MyRat) : a ≤ b ∨ b ≤ a := by
  by_cases h : IsNonneg (b - a)
  · left
    exact h
  · right
    by_cases h2 : IsNonneg (a - b)
    · exact h2
    · exfalso
      apply h
      clear h
      rw [(show b - a = -(a - b) by ring)]
      apply nonneg_neg_of_not_nonneg h2

noncomputable instance : LinearOrder MyRat where
  le_total := le_total
  decidableLE := Classical.decRel _

lemma mul_pos (a b : MyRat) (ha : 0 < a) (hb : 0 < b) : 0 < a * b := by
  rw [lt_iff_le_and_ne] at ha hb ⊢
  rcases ha with ⟨ha, ha'⟩
  rcases hb with ⟨hb, hb'⟩
  refine ⟨?_, by aesop⟩
  rw [zero_le_iff_IsNonneg] at  ha hb ⊢
  apply isNonneg_mul_isNonneg ha hb

noncomputable instance : LinearOrderedCommRing MyRat where
  zero_le_one := zero_le_one
  add_le_add_left := add_le_add_left
  mul_pos := mul_pos
  mul_comm := mul_comm
  le_total := le_total
  decidableLE := Classical.decRel _

end MyRat

/-

Both of these now work

#synth LinearOrder MyRat
#synth OrderedRing MyRat

-/
