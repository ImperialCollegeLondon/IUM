import IUM.Nat.Addition

namespace MyNat

@[pp_nodot]
def mul : ℕ → ℕ → ℕ
  | a, 0 => zero
  | a, succ n => add (mul a n) a

instance : HMul ℕ ℕ ℕ where hMul := mul

-- problem sheet 1(a)
Lemma mul_one
  ""
  Given: (m : ℕ)
  Assume:
  Conclusion: m * 1 = m
Proof:
  Calc
    m * 1 = m * succ 0 by rfl -- def of 1
    _     = m * 0 + m  by definition of mul
    _     = 0 + m      by
            apply congr_arg₂ _ ?_ rfl
            apply_def mul
    _     = m          by rw [zero_add]
QED

-- problem sheet 1(b)
Lemma zero_mul
  ""
  Given: (m : ℕ)
  Assume:
  Conclusion: 0 * m = 0
Proof:
  Let's prove this by induction on m
  · Apply definition of mul
  · Fix d : ℕ
    Assume IH : 0 * d = 0
    Calc
      0 * succ d = 0 * d + 0 by definition of mul
      _          = 0 + 0     from IH
      _          = 0         by definition of add
QED

-- problem sheet 1(c)
Lemma succ_mul
  ""
  Given: (a b : ℕ)
  Assume:
  Conclusion: succ a * b = a * b + b
Proof:
  Let's prove this by induction on b
  · Calc
      succ a * 0 = 0         by definition of mul
      _          = 0 + 0     by definition of add
      _          = a * 0 + 0 by
                    apply congr_arg₂ _ ?_ rfl
                    apply_def mul
  · Fix d : ℕ
    Assume IH : succ a * d = a * d + d
    Calc
      succ a * succ d = succ a * d + succ a  by definition of mul
      _               = (a * d + d) + succ a from IH
      _               = a * d + (d + succ a) from add_assoc
      _               = a * d + succ (d + a) by
                            apply congr_arg _ ?_
                            definition of add
      _               = a * d + (succ d + a) from succ_add
      _               = a * d + (a + succ d) from add_comm (succ d) -- FIXME
      _               = (a * d + a) + succ d from add_assoc
      _               = a * succ d + succ d  by
                            apply congr_arg₂ _ ?_ rfl
                            definition of mul
QED

-- problem sheet 1(d)
Lemma mul_comm
  ""
  Given: (a b : ℕ)
  Assume:
  Conclusion: a * b = b * a
Proof:
  Let's prove this by induction on b
  · Calc
      a * 0 = 0     by definition of mul
      _     = 0 * a from zero_mul
  · Fix d : ℕ
    Assume IH : a * d = d * a
    Calc
      a * succ d = a * d + a  by definition of mul
      _          = d * a + a  from IH
      _          = succ d * a from succ_mul
QED

-- problem sheet 1(e)
Lemma one_mul
  ""
  Given: (m : ℕ)
  Assume:
  Conclusion: 1 * m  = m
Proof:
  Calc
    1 * m = m * 1 from mul_comm
    _     = m     from mul_one
QED

-- problem sheet 1(f)
Lemma mul_add
  ""
  Given: (a b c : ℕ)
  Assume:
  Conclusion: a * (b + c) = a * b + a * c
Proof:
  Let's prove this by induction on c
  · Calc
      a * (b + 0) = a * b         by
                      apply congr_arg _ ?_
                      definition of add
      _           = a * b + 0     by definition of add
      _           = a * b + a * 0 by
                      apply congr_arg _ ?_
                      definition of mul
  · Fix d : ℕ
    Assume IH : a * (b + d) = a * b + a * d
    Calc
      a * (b + succ d) = a * succ (b + d)    by
                          apply congr_arg _ ?_
                          definition of add
      _                = a * (b + d) + a     by definition of mul
      _                = (a * b + a * d) + a from IH
      _                = a * b + (a * d + a) from add_assoc
      _                = a * b + a * succ d  by
                          apply congr_arg _ ?_
                          definition of mul
QED

-- problem sheet 1(g)
Lemma add_mul
  ""
  Given: (a b c : ℕ)
  Assume:
  Conclusion: (a + b) * c = a * c + b * c
Proof:
  Calc
    (a + b) * c = c * (a + b)   from mul_comm
    _           = c * a + c * b from mul_add
    _           = a * c + b * c by rw [mul_comm c, mul_comm c] -- FIXME
QED

-- problem sheet 1(h)
Lemma mul_assoc
  ""
  Given: (a b c : ℕ)
  Assume:
  Conclusion: (a * b) * c = a * (b * c)
Proof:
  Let's prove this by induction on c
  · Calc
      (a * b) * 0 = 0           by definition of mul
      _           = a * 0       by definition of mul
      _           = a * (b * 0) by
                          apply congr_arg _ ?_
                          definition of mul
  · Fix d : ℕ
    Assume IH : a * b * d = a * (b * d)
    Calc
      (a * b) * succ d = (a * b) * d + a * b by definition of mul
      _                = a * (b * d) + a * b from IH
      _                = a * (b * d + b) from mul_add
      _                = a * (b * succ d) by
                          apply congr_arg _ ?_
                          definition of mul
QED
