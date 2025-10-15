import IUM.Nat.LE
import IUM.Nat.Multiplication

namespace MyNat


Lemma add_le_add_right
  "Right-addition is monotone"
  Given: {a b : ℕ} (t : ℕ)
  Assume: (h : a ≤ b)
  Conclusion: a + t ≤ b + t
Proof:
  Since ∃ k, b = a + k we get d such that hd : b = a + d
  Let's prove that d works
  Calc
    b + t = (a + d) + t   from hd
    _     = a + (d + t)   from add_assoc
    _     = a + (t + d)   from add_comm d
    _     = (a + t) + d   from add_assoc
QED

Lemma mul_le_mul_right
  "Right-multiplication is monotone"
  Given: {a b : ℕ} (t : ℕ)
  Assume: (h : a ≤ b)
  Conclusion: a * t ≤ b * t
Proof:
  Since ∃ k, b = a + k we get d such that hd : b = a + d
  Let's prove that d * t works
  Calc
    b * t = (a + d) * t   from hd
    _     = a * t + d * t from add_mul
QED
