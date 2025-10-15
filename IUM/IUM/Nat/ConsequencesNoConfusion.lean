import IUM.Nat.Addition
import IUM.Nat.Multiplication
import IUM.Nat.NoJunkNoConfusion

namespace MyNat

/-- Addition is cancellative -/
lemma add_right_cancel' {x y n : ℕ} : x + n = y + n → x = y := by
  induction n with
  | BaseCase =>
    intro h
    calc
      x = x + 0 := by apply_def add
      _ = y + 0 := by rel [h]
      _ = y     := by apply_def add
  | InductiveStep k IH =>
    intro h1
    have h2 :=
      calc
        succ (x + k) = x + succ k   := by apply_def add
        _            = y + succ k   := by rel [h1]
        _            = succ (y + k) := by apply_def add
    apply succ_inj at h2
    exact IH h2

-- ANCHOR: th_add_right_cancel
Lemma add_right_cancel
  "Addition is cancellative"
  Given: {x y n : ℕ}
  Assume:
  Conclusion: x + n = y + n → x = y
Proof:
  Let's prove this by induction on n
  · Assume h : x + 0 = y + 0
    Calc
      x = x + 0 by definition of add
      _ = y + 0 from h
      _ = y     by definition of add
  · Fix k : ℕ
    Assume IH : x + k = y + k → x = y
    Assume h1 : x + succ k = y + succ k
    Fact h2 : succ (x + k) = succ (y + k) by
      Calc
        succ (x + k) = x + succ k   by definition of add
        _            = y + succ k   from h1
        _            = succ (y + k) by definition of add
    By succ_inj applied to h2 we get h3 : x + k = y + k
    We conclude by IH applied to h3
QED
-- ANCHOR_END: th_add_right_cancel

-- ANCHOR: th_add_left_eq_self
Lemma add_left_eq_self
  "Only zero leaves a number unchanged when added"
  Given: {x n : ℕ}
  Assume: (h : x + n = n)
  Conclusion: x = 0
Proof:
  Fact h' : x + n = 0 + n by
    Calc
      x + n = n     from h
      _     = 0 + n from zero_add
  We conclude by add_right_cancel applied to h'
QED
-- ANCHOR_END: th_add_left_eq_self

-- ANCHOR: th_add_left_eq_zero
Lemma add_left_eq_zero
  "If x + y = 0 then y = 0"
  Given: {x y : ℕ}
  Assume: (h : x + y = 0)
  Conclusion: y = 0
Proof:
  By zero_or_succ applied to y we get hy₀ : y = 0 ∨ ∃ n, y = succ n
  We discuss depending on whether y = 0 or ∃ n, y = succ n
  · Assume hy : y = 0
    We conclude by hy
  · Assume hy : ∃ n, y = succ n
    Since ∃ n, y = succ n we get n such that hyn : y = succ n
    Fact hxn : 0 = succ (x + n) by
      Calc
        0 = x + y        from h
        _ = x + succ n   from hyn
        _ = succ (x + n) by definition of add
    By zero_ne_succ applied to x + n we get hxn' : 0 ≠ succ (x + n)
    contradiction
QED
-- ANCHOR_END: th_add_left_eq_zero

-- ANCHOR: th_add_right_eq_zero
Lemma add_right_eq_zero
  "If x + y = 0 then x = 0"
  Given: {x y : ℕ}
  Assume: (h : x + y = 0)
  Conclusion: x = 0
Proof:
  By add_left_eq_zero applied to h we get hy : y = 0
  Calc
    x = x + 0 by definition of add
    _ = x + y from hy
    _ = 0     from h
QED
-- ANCHOR_END: th_add_right_eq_zero

Lemma eq_zero_of_mul_eq_zero
  ""
  Given: {a y : ℕ}
  Assume: (h : a * y = 0) (hy : y ≠ 0)
  Conclusion: a = 0
Proof:
  By eq_succ_of_ne_zero applied to hy we get hy' : ∃ k, y = succ k
  By hy' we get k such that hyk : y = succ k
  Fact hak : a * k + a = 0 by
    Calc
      a * k + a = a * succ k by definition of mul
      _         = a * y      from hyk
      _         = 0          from h
  We conclude by add_left_eq_zero applied to hak
QED


Lemma mul_eq_zero
  "The natural numbers are an integral domain"
  Given: {x y : ℕ}
  Assume: (h : x * y = 0)
  Conclusion: x = 0 ∨ y = 0
Proof:
  have := eq_zero_of_mul_eq_zero h
  tauto
QED

Lemma mul_right_cancel
  "Multiplication by a nonzero number is cancellative"
  Given: {a x : ℕ}
  Assume: (hx : x ≠ 0)
  Conclusion: ∀ {b}, a * x = b * x → a = b
Proof:
  Let's prove this by induction on a
  · Fix b : ℕ
    Assume h : 0 * x = b * x
    Fact h' : b * x = 0 by
      Calc
        b * x = 0 * x from h
        _     = 0     from zero_mul
    We conclude by eq_zero_of_mul_eq_zero applied to h' and hx
  · Fix d : ℕ
    Assume IH : ∀ {b : ℕ}, d * x = b * x → d = b
    Fix b : ℕ
    Assume hb : succ d * x = b * x
    By zero_or_succ applied to b we get hb₀ : b = 0 ∨ ∃ e, b = succ e
    We discuss depending on whether b = 0 or ∃ e, b = succ e
    · Assume hb₀ : b = 0
      rename_i h
      clear h
      We rewrite using hb₀ at hb ⊢
      clear hb₀ b
      Fact hdn : succ d * x = 0 by
        Calc
          succ d * x = 0 * x from hb
          _          = 0 from zero_mul
      We conclude by eq_zero_of_mul_eq_zero applied to hdn and hx
    · Assume hb₀ : ∃ e, b = succ e
      rename_i h
      clear h
      By hb₀ we get e such that he : b = succ e
      We rewrite using he at hb ⊢
      Fact hde : d * x + x = e * x + x by
        Calc
          d * x + x = succ d * x from succ_mul
          _         = succ e * x from hb
          _         = e * x + x  from succ_mul
      By add_right_cancel applied to hde we get hde' : d * x = e * x
      By IH applied to hde' we get hde''
      We conclude by hde''
QED
