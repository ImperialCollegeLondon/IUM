/-
Copyright (c) 2025 Heather Macbeth, based on prior versions by Marie-Amélie Lawn and Kevin Buzzard.
All rights reserved.
-/
import LectureNotes.Formatting

open Verso.Genre Manual
open Verso.Code.External

set_option verso.exampleProject "../IUM"
set_option verso.exampleModule "IUM.LE"
set_option verso.externalExamples.suppressedNamespaces "MyNat"

#doc (Manual) "The ordering on the naturals"  =>

We did not need Peano's extra axioms to develop the theory of addition and multiplication, but we will need them to develop the theory of $`\leq`
(this is not surprising: if there was some weird loop in the natural numbers then $`\leq` would not satisfy basic properties which we require from it like transitivity).

Here are the definitions.

:::definition (title := "The ordering on the naturals")
Let $`x` and $`y` be natural numbers.
We say that $`x\leq y` if there exists a natural number $`n` such that $`y=x+n`.
:::

Let's do some warm-up exercises.

:::lemma "le_basic"
Let $`x` be a natural number. Then
1. $`0\leq x;`
2. $`x\leq x;`
3. $`x\leq S(x);`
4. If $`x\leq 0` then $`x=0`.
:::

:::proof
1. What does the question _mean_?
By _definition_ of $`\leq` we need to prove that there exists a natural number $`n` such that $`x=0+n`.
We can choose $`n` to be whatever we like, so let's choose $`n=x` and now we have to prove $`x=0+x`.
But we already proved this in {theoremref "zero_add"}[].
2. Similarly here, the question means that we have to prove there exists a natural number $`n` such that $`x=x+n`.
Just take $`n=0`, because $`x+0=x` by definition of addition.
3. The question means that we have to prove that there exists $`n` such that $`S(x)=x+n`.
But we know $`S(x)=x+1` from {theoremref "succ_eq_add_one"}[], so $`n=1` will work.
4. Say $`x\leq 0`.
Then by definition, there is some natural number $`n` such that $`x+n=0`.
By {theoremref "le_prereq2"}[] we deduce $`x=n=0` and in particular $`x=0`.
:::

```anchor th_zero_le
Lemma zero_le
  "0 is no bigger than any other natural"
  Given: (x : ℕ)
  Assume:
  Conclusion: 0 ≤ x
Proof:
  Let's prove that ∃ n : ℕ, x = 0 + n
  Let's prove that x works
  We conclude by zero_add
QED
```

```anchor th_le_refl
Lemma le_refl
  "A natural number is no bigger than itself"
  Given: (x : ℕ)
  Assume:
  Conclusion: x ≤ x
Proof:
  Let's prove that ∃ n : ℕ, x = x + n
  Let's prove that 0 works
  Apply definition of add
QED
```

```anchor th_le_succ_self
Lemma le_succ_self
  "A natural number is no bigger than its successor"
  Given: (x : ℕ)
  Assume:
  Conclusion: x ≤ succ x
Proof:
  Let's prove that ∃ n : ℕ, succ x = x + n
  Let's prove that 1 works
  We conclude by succ_eq_add_one
QED
```

```anchor th_le_zero
Lemma le_zero
  "Only 0 is no bigger than 0"
  Given: {x : ℕ}
  Assume: (hx : x ≤ 0)
  Conclusion: x = 0
Proof:
  Since ∃ n, 0 = x + n we get n such that hxn : 0 = x + n
  Since 0 = x + n we get hxn' : x + n = 0
  We conclude by add_right_eq_zero applied to hxn'
QED
```

The main theorem that we want is that $`\leq` is a total order on $`\N`.
Let's recall what this means.

:::theorem "linear_order" (title := "≤ is a total order")
Say $`x,y,z\in\N`.
1. $`x\leq x` (reflexivity);
2. If $`x\leq y` and $`y\leq z` then $`x\leq z` (transitivity);
3. If $`x\leq y` and $`y\leq x` then $`x=y` (antisymmetry);
4. Either $`x\leq y` or $`y\leq x` (totality).
:::

:::proof
We've already done the first part;
I'll leave the next two to you, and will do the last one.

1.  This is {theoremref "le_basic"}[](2).
2.  For this one you can _assume_ that $`x\leq y` and $`y\leq z`, and you need to _prove_ that $`x\leq z`.
Use the definition of $`\leq` and finish the proof as an exercise.
3.  Don't use induction -- use {theoremref "le_prereq"}[] and {theoremref "le_prereq2"}[].
4.  This one is fiddly!
    Let's fix $`x` and do induction on $`y`.
    Formally, the statement $`P_n` we're proving by induction on $`n` is that $`x\leq n` or $`n\leq x`.
    For the base case we need to prove $`x\leq 0` or $`0\leq x`.
    But we already proved in {theoremref "le_basic"}[](1) that $`0\leq x`, and this finishes the base case.

    For the inductive step, we may assume $`x\leq n` or $`n\leq x`, and we want to prove $`x\leq S(n)` or $`S(n)\leq x`.
    Our assumption says that one of two things is true; let's deal with the two cases separately.

    The first case is where $`x\leq n`.
    We need to prove $`x\leq S(n)` or $`S(n)\leq x`.
    Let's prove $`x\leq S(n)`;
    this follows from $`x\leq n` (our assumption),
    $`n\leq S(n)` ({theoremref "le_basic"}[](3)),
    and transitivity (part 2 of this lemma).

    The second case is the trickiest part of the proof.
    We assume $`n\leq x` and we need to deduce that either $`x\leq S(n)` or $`S(n)\leq x`.
    The reason this is the hardest case is that we still don't know which of these is going to be true;
    if $`x=n` then the first one will be true, and if $`x` is much bigger than $`n` then it will be the second one, so we have to break things down even further.
    We know $`n\leq x` so we know there exists $`y` such that $`x=n+y`.
    We also know that $`y` is either $`0` or of the form $`S(t)` for some natural $`t`.
    So let's do a final case split and finish this problem.

    If $`y=0` then $`x=n+0=n`, so we can prove $`x\leq S(n)`;
    indeed $`n\leq S(n)` was proved already in {theoremref "le_basic"}[](3).

    Finally, if $`y=S(t)` then $`x=n+S(t)=S(n+t)=S(n)+t` by definition of $`+` and {theoremref "succ_add"}[], and this means that $`S(n)\leq x` by definition of $`\leq`.
:::

```anchor th_le_total
Lemma le_total
  "Totality of ≤"
  Given: (x y : ℕ)
  Assume:
  Conclusion: x ≤ y ∨ y ≤ x
Proof:
  Let's prove this by induction on y
  · Let's prove that 0 ≤ x
    We conclude by zero_le
  · Fix n : ℕ
    Assume hn : x ≤ n ∨ n ≤ x
    We discuss depending on whether x ≤ n or n ≤ x
    · Assume hxn : x ≤ n
      Let's prove that x ≤ succ n
      Calc
        x ≤ n      from hxn
        _ ≤ succ n from le_succ_self
    · Assume hnx : n ≤ x
      Since ∃ y, x = n + y we get y such that hxe : x = n + y
      By zero_or_succ applied to y we get he : y = 0 ∨ ∃ t, y = succ t
      We discuss depending on whether y = 0 or ∃ t, y = succ t
      · Assume hy : y = 0
        Let's prove that x ≤ succ n
        Calc
          x = n + y  from hxe
          _ = n + 0  from hy
          _ = n      by definition of add
          _ ≤ succ n from le_succ_self
      · Assume hy : ∃ t, y = succ t
        Since ∃ t, y = succ t we get t such that ht : y = succ t
        Let's prove that ∃ s, x = succ n + s
        Let's prove that t works
        Calc
          x = n + y        from hxe
          _ = n + succ t   from ht
          _ = succ (n + t) by definition of add
          _ = succ n + t   from succ_add
QED
```

-- Interaction between $`\leq` and $`+`, $`\times`
:::theorem "le_add_mul"
Let $`a`, $`b` and $`x` be natural numbers.
1. If $`a\leq b` then $`a+x\leq b+x`.
2. If $`a\leq b` then $`a\times x\leq b\times x`.
:::

:::proof
Here is a sketch.
You should check that you can fill in the details, and that I definitely didn't assume anything which we didn't prove yet.
1. Choose $`n` such that $`b=a+n`.
Now check that $`(b+x)=(a+x)+n`.
2. Choose $`n` such that $`b=a+n`.
Now check that $`bx=ax+nx`.
:::
