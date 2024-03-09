import Mathbin.Tactic.Default

#align_import «2020».integers.int_def_solns

/-- The equivalence relation on ℕ² such that equivalence classes are ℤ -/
def Nat2.R (a b : ℕ × ℕ) : Prop :=
  a.1 + b.2 = b.1 + a.2

-- here a and b are pairs, so a = (a.1, a.2) etc.
-- introduce ≈ (type with `\~~`) notation for this relation
instance : HasEquiv (ℕ × ℕ) :=
  ⟨Nat2.R⟩

-- let's prove some lemmas about this binary relation
namespace Nat2.R

#check Quotient.liftOn

-- The following lemma is true by definition, but it's useful to
-- have it around so you can rewrite with it
@[simp]
theorem equiv_def {i j k l : ℕ} : (i, j) ≈ (k, l) ↔ i + l = k + j := by rfl

-- try rewriting `equiv_def`
theorem practice : (3, 5) ≈ (4, 6) := by
  change 3 + 6 = 4 + 5
  rfl

-- Now let's prove that this binary relation is an equivalence relation
theorem reflexive : ∀ x : ℕ × ℕ, x ≈ x := by
  rintro ⟨i, j⟩
  rw [equiv_def]

theorem symmetric : ∀ x y : ℕ × ℕ, x ≈ y → y ≈ x :=
  by
  -- here are a couple of tricks
  rintro ⟨i, j⟩ ⟨k, l⟩ h
  -- type `⊢` with `\|-`
  rw [equiv_def] at h ⊢
  rw [h]

theorem transitive : ∀ x y z : ℕ × ℕ, x ≈ y → y ≈ z → x ≈ z :=
  by
  -- this is a little trickier
  -- recall `add_right_inj` says `a + b = c + b → a = c`
  rintro ⟨i, j⟩ ⟨k, l⟩ ⟨m, n⟩ hxy hyz
  rw [equiv_def] at hxy hyz ⊢
  rw [← add_left_inj (k + l)]
  calc
    i + n + (k + l) = i + l + (k + n) := by ring
    _ = k + j + (m + l) := by rw [hxy, hyz]
    _ = m + j + (k + l) := by ring

-- This line tells Lean that the binary relation is an equivalence
-- relation and hence we can take the "quotient", i.e. the
-- type of equivalence classes
instance setoid : Setoid (ℕ × ℕ) where
  R := Nat2.R
  iseqv := ⟨reflexive, symmetric, transitive⟩

-- end of lemmas about the binary relation
end Nat2.R

-- ...but we're still going to be using them
open Nat2.R

/-- The integers are the equivalence classes of the equivalence relation
 we just defined on ℕ²  -/
def Myint :=
  Quotient Nat2.R.setoid

-- let's make some definitions, and prove some theorems, about integers
namespace Myint

/-! ## zero -/


-- The first goal is to get a good interface for addition.
-- To do this we need to define a+b, and -a, and 0. Let's do
-- them in reverse order.
def zero :=
  ⟦(0, 0)⟧

instance : Zero Myint :=
  ⟨Myint.zero⟩

theorem zero_def : (0 : Myint) = ⟦(0, 0)⟧ := by rfl

/-! ## negation (additive inverse) -/


-- First we define an "auxiliary" map from ℕ² to ℤ 
-- sending (a,b) to the equivalence class of (b,a).
def negAux (x : ℕ × ℕ) : Myint :=
  ⟦(x.2, x.1)⟧

-- true by definition
theorem negAux_def (i j : ℕ) : negAux (i, j) = ⟦(j, i)⟧ :=
  rfl

/-! ### Well-definedness

OK now here's the concrete problem. We would like to define
a negation map `ℤ → ℤ` sending `z` to `-z`. We want to do this in
the following way: Say `z ∈ ℤ`. Choose `a=(i,j) ∈ ℕ²` representing `z`
(i.e. such that `cl(i,j) = ⟦(i,j)⟧ = z`)
Now apply `neg_aux` to `a`, and define `-z` to be the result.

The problem with this is that what if `b` is a different
element of the equivalence class? Then we also want `-z` to be `neg_aux b`.

Indeed, in Lean this construction is called `quotient.lift`, and
if you uncomment the below code
-/


--def neg : myint → myint :=
--quotient.lift neg_aux _
/-
you'll see an error, and if you put your cursor on the error you'll
see that Lean wants a proof that if two elements `a` and `b` are in the
same equivalence class, then `neg_aux a = neg_aux b`. So let's prove this now.
-/
-- negation on the integers, defined via neg_aux, is well-defined.
theorem negAux_lemma : ∀ x y : ℕ × ℕ, x ≈ y → negAux x = negAux y :=
  by
  rintro ⟨i, j⟩ ⟨k, l⟩ h
  rw [neg_aux_def, neg_aux_def]
  -- ⊢ ⟦(j, i)⟧ = ⟦(l, k)⟧
  -- next step: if ⟦a⟧=⟦b⟧ then a ≈ b
  apply Quotient.sound
  -- ⊢ (j, i) ≈ (l, k)
  rw [equiv_def] at h ⊢
  rw [add_comm]
  rw [← h]
  apply add_comm

/-- Negation on on the integers. The function sending `z` to `-z`. -/
def neg : Myint → Myint :=
  Quotient.lift negAux negAux_lemma

-- notation for negation
instance : Neg Myint :=
  ⟨neg⟩

-- this is true by definition
theorem neg_def (i j : ℕ) : (-⟦(i, j)⟧ : Myint) = ⟦(j, i)⟧ := by rfl

/-!  ## addition

Our final construction: we want to define addition on `myint`. 
Here we have the same problem. Say z₁ and z₂ are integers.
Choose elements a₁=(i,j) and a₂=(k,l) in ℕ². We want to define
z₁ + z₂ to be ⟦(i+k,j+l)⟧, the equivalence class of a₁ + a₂.
Let's make this definition now.

-/


/-- An auxiliary function taking two elements of ℕ² and returning
the equivalence class of their sum. -/
def addAux (x y : ℕ × ℕ) : Myint :=
  ⟦(x.1 + y.1, x.2 + y.2)⟧

-- true by definition, but useful for rewriting
theorem addAux_def (i j k l : ℕ) : addAux (i, j) (k, l) = ⟦(i + k, j + l)⟧ := by rfl

/-

We want the definition of addition to look like the below.
Uncomment it to see the problem. 

-/
--def add : myint → myint → myint :=
--quotient.lift₂ add_aux _
/-
We had better check that choosing different elements in the same
equivalence class gives the same definition.

-/
theorem addAux_lemma : ∀ x₁ x₂ y₁ y₂ : ℕ × ℕ, x₁ ≈ y₁ → x₂ ≈ y₂ → addAux x₁ x₂ = addAux y₁ y₂ :=
  by
  rintro ⟨a, b⟩ ⟨c, d⟩ ⟨e, f⟩ ⟨g, h⟩ h1 h2
  rw [add_aux_def]
  rw [add_aux_def]
  apply Quotient.sound
  rw [equiv_def] at *
  rw [show a + c + (f + h) = a + f + (c + h) by ring]
  rw [h1, h2]
  ring

-- Now this is checked, we can define addition.
/-- Addition on the integers -/
def add : Myint → Myint → Myint :=
  Quotient.lift₂ addAux addAux_lemma

-- notation for addition
instance : Add Myint :=
  ⟨add⟩

-- true by definition
theorem add_def (i j k l : ℕ) : (⟦(i, j)⟧ + ⟦(k, l)⟧ : Myint) = ⟦(i + k, j + l)⟧ := by rfl

/-
The four fundamental facts about addition on the integes are:
1) associativity
2) commutativity
3) zero is an additive identity
4) negation is an additive inverse.

Let's prove these now.

-/
theorem zero_add (x : Myint) : 0 + x = x :=
  by
  apply Quotient.inductionOn x
  rintro ⟨a, b⟩
  rw [zero_def]
  rw [add_def]
  apply Quotient.sound
  rw [equiv_def]
  ring

theorem add_zero (x : Myint) : x + 0 = x :=
  by
  apply Quotient.inductionOn x
  rintro ⟨a, b⟩
  rw [zero_def]
  rw [add_def]
  apply Quotient.sound
  rw [equiv_def]
  ring

theorem add_left_neg (x : Myint) : -x + x = 0 :=
  by
  apply Quotient.inductionOn x
  rintro ⟨a, b⟩
  rw [zero_def]
  rw [neg_def]
  rw [add_def]
  apply Quotient.sound
  rw [equiv_def]
  ring

theorem add_comm (x y : Myint) : x + y = y + x :=
  by
  apply Quotient.induction_on₂ x y
  rintro ⟨a, b⟩ ⟨c, d⟩
  rw [add_def, add_def]
  apply Quotient.sound
  rw [equiv_def]
  ring

theorem add_assoc (x y z : Myint) : x + y + z = x + (y + z) :=
  by
  apply Quotient.induction_on₃ x y z
  rintro ⟨a, b⟩ ⟨c, d⟩ ⟨e, f⟩
  simp [add_def]
  ring

-- We just proved that the integers are a commutative group under addition!
instance : AddCommGroup Myint where
  add := (· + ·)
  add_assoc := add_assoc
  zero := 0
  zero_add := zero_add
  add_zero := add_zero
  neg := Neg.neg
  add_left_neg := add_left_neg
  add_comm := add_comm

/-! ## multiplication

What's left to define is 1 and multiplication (note that we don't need multiplicative
inverses -- if a is a non-zero integer then a⁻¹ is typially not an integer)

-/


-- woohoo!
def mulAux (x y : ℕ × ℕ) : Myint :=
  ⟦(x.1 * y.1 + x.2 * y.2, x.1 * y.2 + x.2 * y.1)⟧

theorem mulAux_def (i j k l : ℕ) : mulAux (i, j) (k, l) = ⟦(i * k + j * l, i * l + j * k)⟧ := by rfl

-- Boss level. 
-- Dr. Lawn: "We leave the similar verification for multiplication as an exercise."
-- This is what we need to check for multiplication to "descend" (or "lift" as Lean
-- calls it) to a well-defined function on the quotient.
theorem mulAux_lemma : ∀ x₁ x₂ y₁ y₂ : ℕ × ℕ, x₁ ≈ y₁ → x₂ ≈ y₂ → mulAux x₁ x₂ = mulAux y₁ y₂ :=
  by
  rintro ⟨a, b⟩ ⟨c, d⟩ ⟨e, f⟩ ⟨g, h⟩ h1 h2
  simp only [mul_aux_def]
  apply Quotient.sound
  rw [equiv_def] at *
  -- a calc proof would be nicer. Can I get away with rewriting h1 and h2
  -- fewer times?
  rw [← add_left_inj (a * h)]
  have h3 : a * c + b * d + (e * h + f * g) + a * h = a * (c + h) + b * d + e * h + f * g
  ring
  rw [h3]
  rw [h2]
  have h4 : a * (g + d) + b * d + e * h + f * g = (a + f) * g + a * d + b * d + e * h
  ring
  rw [h4]
  rw [h1]
  clear h3; clear h4
  rw [show (e + b) * g + a * d + b * d + e * h = e * g + a * d + b * (g + d) + e * h by ring]
  rw [← h2]
  rw [show e * g + a * d + b * (c + h) + e * h = e * g + a * d + b * c + (e + b) * h by ring]
  rw [← h1]
  ring

-- definition of multiplication
def mul : Myint → Myint → Myint :=
  Quotient.lift₂ mulAux mulAux_lemma

instance : Mul Myint :=
  ⟨mul⟩

theorem hMul_def (i j k l : ℕ) : (⟦(i, j)⟧ * ⟦(k, l)⟧ : Myint) = ⟦(i * k + j * l, i * l + j * k)⟧ :=
  by rfl

theorem hMul_assoc (x y z : Myint) : x * y * z = x * (y * z) :=
  by
  apply Quotient.induction_on₃ x y z
  rintro ⟨a, b⟩ ⟨c, d⟩ ⟨e, f⟩
  simp [mul_def]
  ring

def one : Myint :=
  ⟦(37, 36)⟧

instance : One Myint :=
  ⟨Myint.one⟩

-- true by definition
theorem one_def : (1 : Myint) = ⟦(37, 36)⟧ := by rfl

theorem one_hMul (x : Myint) : 1 * x = x :=
  by
  apply Quotient.inductionOn x
  rintro ⟨i, j⟩
  simp [one_def, mul_def]
  ring

theorem hMul_one (x : Myint) : x * 1 = x :=
  by
  apply Quotient.inductionOn x
  rintro ⟨i, j⟩
  simp [one_def, mul_def]
  ring

theorem hMul_comm (x y : Myint) : x * y = y * x :=
  by
  apply Quotient.induction_on₂ x y
  rintro ⟨i, j⟩ ⟨k, l⟩
  simp [mul_def]
  ring

theorem hMul_add (x y z : Myint) : x * (y + z) = x * y + x * z :=
  by
  apply Quotient.induction_on₃ x y z
  rintro ⟨i, j⟩ ⟨k, l⟩ ⟨m, n⟩
  simp [add_def, mul_def]
  ring

theorem add_hMul (x y z : Myint) : (x + y) * z = x * z + y * z :=
  by
  apply Quotient.induction_on₃ x y z
  rintro ⟨i, j⟩ ⟨k, l⟩ ⟨m, n⟩
  simp [add_def, mul_def]
  ring

-- The integers are a commutative ring
-- (that is, they satisfy the axioms we just proved)
instance : CommRing Myint :=
  { Myint.addCommGroup with
    mul := (· * ·)
    mul_assoc := hMul_assoc
    one := 1
    one_mul := one_hMul
    mul_one := hMul_one
    left_distrib := hMul_add
    right_distrib := add_hMul
    mul_comm := hMul_comm }

end Myint

