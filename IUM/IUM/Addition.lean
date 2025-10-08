import Verbose.English.All
import IUM.Definition
import IUM.Config.ApplyDef

set_option autoImplicit false

namespace MyNat

@[pp_nodot]
-- ANCHOR: def_add
def add : ℕ → ℕ → ℕ
  | a, 0 => a
  | a, succ n => succ (add a n)
-- ANCHOR_END: def_add

instance : HAdd ℕ ℕ ℕ where hAdd := MyNat.add

-- This one needs some work
Lemma one_plus_one
  "1 + 1 = 2"
  Given:
  Assume:
  Conclusion: 1 + 1 = 2
Proof:
  Calc
    1 + 1 = 1 + succ 0 by
                  refine congr_arg _ ?_
                  unfold_projs
                  with_reducible rfl
    _     = succ (1 + 0) by definition of add
    _     = succ 1 by
                apply congr_arg _ ?_
                apply_def add
    _     = 2 by
                unfold_projs -- maybe `unfold_projs OfNat`?
                with_reducible rfl
QED

-- This one needs some work too
Lemma succ_eq_add_one
  ""
  Given: (n : ℕ)
  Assume:
  Conclusion: succ n = n + 1
Proof:
  Calc
    succ n = succ (n + 0) by
                apply congr_arg _ ?_
                apply_def add
    _      = n + succ 0 by definition of add
    _      = n + 1 by
                apply congr_arg _ ?_
                unfold_projs
                with_reducible rfl
QED

-- ANCHOR: th_zero_add
Lemma zero_add
  "Adding 0 on the left"
  Given: (x : ℕ)
  Assume:
  Conclusion: 0 + x = x
Proof:
  Let's prove this by induction on x
  · Apply definition of add
  · Fix n : ℕ
    Assume IH : 0 + n = n
    Calc
      0 + succ n = succ (0 + n) by definition of add
      _          = succ n       from IH
QED
-- ANCHOR_END: th_zero_add

-- ANCHOR: th_succ_add
Lemma succ_add
  "Adding a successor on the left"
  Given: (a b : ℕ)
  Assume:
  Conclusion: succ a + b = succ (a + b)
Proof:
  Let's prove this by induction on b
  · Calc
      succ a + 0 = succ a       by definition of add
      _          = succ (a + 0) by
            refine congr_arg _ ?_
            apply_def add
  · Fix k : ℕ
    Assume IH : succ a + k = succ (a + k)
    Calc
      succ a + succ k = succ (succ a + k)   by definition of add
      _               = succ (succ (a + k)) from IH
      _               = succ (a + succ k)   by
                          apply congr_arg _ ?_
                          apply_def add
QED
-- ANCHOR_END: th_succ_add

-- ANCHOR: th_add_comm
Lemma add_comm
  "Addition is commutative"
  Given: (a b : ℕ)
  Assume:
  Conclusion: a + b = b + a
Proof:
  Let's prove this by induction on b
  · Calc
      a + 0 = a     by definition of add
      _     = 0 + a from zero_add
  · Fix n : ℕ
    Assume IH : a + n = n + a
    Calc
      a + succ n = succ (a + n) by definition of add
      _          = succ (n + a) from IH
      _          = succ n + a   from succ_add
QED
-- ANCHOR_END: th_add_comm

Lemma add_assoc
  "Addition is associative"
  Given: (a b c : ℕ)
  Assume:
  Conclusion: (a + b) + c = a + (b + c)
Proof:
  Let's prove this by induction on c
  · Calc
      (a + b) + 0 = a + b       by definition of add
      _           = a + (b + 0) by
                        apply congr_arg _ ?_
                        apply_def add
  · Fix k : ℕ
    Assume IH : (a + b) + k = a + (b + k)
    Calc
      (a + b) + succ k = succ ((a + b) + k) by definition of add
      _                = succ (a + (b + k)) from IH
      _                = a + succ (b + k) by definition of add
      _                = a + (b + succ k) by
                          apply congr_arg _ ?_
                          apply_def add
QED
