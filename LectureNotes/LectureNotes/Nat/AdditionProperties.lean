/-
Copyright (c) 2025 Heather Macbeth, based on prior versions by Marie-Amélie Lawn and Kevin Buzzard.
All rights reserved.
-/
import LectureNotes.Formatting

open Verso.Genre Manual
open Verso.Code.External

set_option verso.exampleProject "../IUM"
set_option verso.exampleModule "IUM.Addition"
set_option verso.externalExamples.suppressedNamespaces "MyNat"

#doc (Manual) "Basic properties of addition"  =>

We know that $`x + 0 = x`.
Indeed this is how we _defined_ addition.
But what about $`0 + x`?
Well obviously $`a+b = b+a` so $`0+x` is just $`x+0` which is $`x`.
Why is this argument not allowed?

The reason is that we are _not allowed_ to say "obviously $`a+b = b+a`" -- we have to prove this!
It might be "obvious" from some physical intuition which you have,
but we are in the mathematical universe here and there is no physics for you to rely on.
In fact deducing $`0+x = x` from $`a+b = b+a` is no good –-
it is another example of a _circular argument_,
because $`a+b = b+a` is a tricky puzzle,
and it needs $`0+x = x` as an input,
so we will have to prove $`0 + x = x` first.

Let’s go back to "that’s it",
and write down explicitly what it tells us in the case when we want to _prove_ something.

:::axiom "ind" (title := "Principle of mathematical induction")
Say we have infinitely many true-false mathematical statements $`P_0`, $`P_1`, $`P_2`, $`P_3`, $`\ldots`, and we want to prove them all.
Then it suffices to do the following two things:
* (Base case) Prove that $`P_0` is true;
* (Inductive step) Prove that if $`P_n` is true, then $`P_{S(n)}` is true.
:::

In the second case, when proving $`P_{S(n)}`,
we often refer to our assumption $`P_n` as "the inductive hypothesis".
Let's use this principle to prove a _lemma_, which is a simple theorem.

:::lemma "zero_add"
If $`x` is a natural number, then $`0 + x = x`.
:::

:::proof
We use induction on $`x`.
Formally we let $`P_x` be the statement that $`0 + x = x`
and we use the above principle to prove that $`P_x` is true for all $`x`.
To prove $`P_0` we need to prove that $`0 + 0 = 0`,
but this follows from the definition of addition.
In the inductive step,
we may assume that $`0 + n = n` and we want to now deduce that $`0 + S(n) = S(n)`.
This follows from the following calculation:
$$`\begin{aligned}
0 + S(n) &= S(0 + n) &&\text{by definition of addition} \\
&=S(n) &&\text{by the inductive hypothesis}
\end{aligned}`
:::

```anchor th_zero_add
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
```

We also know that $`a + S(x) = S(a + x)`,
but what about $`S(a) + x`?
Can we prove that this is $`S(a + x)`?
This is the last remaining piece we need in order to prove commutativity of addition.

:::lemma "succ_add"
If $`a` and $`x` are natural numbers, then $`S(a)+x=S(a+x)`.
:::

:::proof
Exercise!
Hint: imagine that $`a` is fixed, let $`P_x` be the statement that $`S(a)+x=S(a+x)`, and use induction on $`x`.
:::

We're now ready to prove _commutativity of addition on the natural numbers_,
which is a fancy way of saying $`x+y=y+x`.

-- Commutativity of addition on $`\N`
:::theorem "add_comm" (title := "Commutativity of addition")
If $`a` and $`b` are natural numbers, than $`a+b=b+a`.
:::

:::proof
We fix $`a` and use induction on $`b`.

The base case: we need to show $`a+0=0+a`.
But $`a+0=a` by definition of addition, and $`0+a=a` by {theoremref "zero_add"}[], so we are done.

The inductive step: we can assume $`a+n=n+a` and we want to prove $`a+S(n)=S(n)+a`.
We do this as follows.
$$`\begin{align*}
a+S(n)&=S(a+n)&& \mathrm{by\ definition\ of\ }+\\
&=S(n+a)&& \mathrm{by\ the\ inductive\ hypothesis}\\
&=S(n)+a&& \mathrm{by\ Lemma\ 9}.
\end{align*}`
:::

```anchor th_add_comm
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
```

It is remarkable to think that all of modern pure mathematics can be built up in this way.
But it can.

We've talked about adding two numbers, but what about adding three numbers?
What does $`a+b+c` mean?
This is an _ambiguous term_!
It could either mean $`(a+b)+c` or $`a+(b+c)`.
These are "obviously" the same, but that's no good!
We need to _prove_ it from the axioms.
The pompous name that mathematicians give to this property is _associativity_ of addition.

:::theorem "add_assoc" (title := "Associativity of addition")
If $`a,b,c` are natural numbers, then $`(a+b)+c=a+(b+c)`.
:::

:::proof
Exercise! Hint: fix $`a` and $`b`, and do induction on $`c`.
:::

Exercise: by means of an explicit example, show that subtraction is not associative (don't worry about the fact that we haven't defined subtraction yet).
