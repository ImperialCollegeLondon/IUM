/-
Copyright (c) 2025 Heather Macbeth, based on prior versions by Marie-Amélie Lawn and Kevin Buzzard.
All rights reserved.
-/
import LectureNotes.Formatting

open Verso.Genre Manual
open Verso.Code.External

set_option verso.exampleProject "../IUM"
set_option verso.exampleModule "IUM.ConsequencesNoConfusion"
set_option verso.externalExamples.suppressedNamespaces "MyNat"

#doc (Manual) "Consequences of these new results"  =>

The results above are the first theorems that we have seen in this chapter of the form "if some equation is true, then some other equation is also true";
results like commutativity and associativity of addition and multiplication were of the form "this equation is always true", and hence logically simpler.
Let's prove some other results of the form "if some equation is true, then some other equation is also true",
using Peano's last two axioms $`S(x)=S(y)\implies x=y` and $`S(x)\neq 0.`

:::theorem "le_prereq"
Say $`x, y` and $`n` are natural numbers.
1. If $`x+n=y+n` then $`x=y` (the cancellation property for addition);
2. If $`x+n=n`, then $`x=0`.
:::

:::proof
1.  Fix $`x` and $`y`, and let's do induction on $`n`.
More precisely, we let $`P_n` denote the statement "if $`x+n=y+n` then $`x=y`"
and we prove $`P_n` for all $`n`, by induction.

    The base case is easy: if $`x+0=y+0` then $`x=y` because $`x+0=x` and $`y+0=y` by definition of addition.
    For the inductive step, we assume "if $`x+k=y+k` then $`x=y`" and we have to prove "if $`x+S(k)=y+S(k)` then $`x=y`".
    So let's assume $`x+S(k)=y+S(k)`; by definition of addition we deduce $`S(x+k)=S(y+k)`.
    By injectivity of $`S` (Peano's second extra axiom, which we proved above) we deduce $`x+k=y+k`.
    And finally by our inductive hypothesis we conclude $`x=y`.

2. Setting $`y=0` in the previous part gives $`x+n=0+n\implies x=0`, and because we know $`0+n=n` we're done.
:::

```anchor th_add_right_cancel
Lemma add_right_cancel
  "Addition is cancellative"
  Given: {x y n : ℕ}
  Assume: (h : x + n = y + n)
  Conclusion: x = y
Proof:
  Let's prove this by induction on n
  · Calc
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
```

```anchor th_add_left_eq_self
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
```

:::theorem "le_prereq2"
Suppose $`x` and $`y` are natural numbers and $`x+y=0`.
Then $`x=y=0`.
:::

:::proof
Let's first prove that $`y=0`.
We showed in {theoremref "zero_or_succ"}[] that $`y` was either $`0` or a successor.
If $`y=0` then we are done.
Otherwise we must have $`y=S(n)` for some natural number $`n`.
In this case $`0=x+y=x+S(n)=S(x+n)`,
but on the other hand, from Peano's first extra axiom, $`0\ne S(x+n)`.
This is a contradiction!
So the $`y=S(n)` case is ruled out.

We deduce that $`y=0`, and hence $`x+0=0` which implies that $`x=0` by definition of addition.
:::

```anchor th_add_left_eq_zero
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
```

```anchor th_add_right_eq_zero
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
```
