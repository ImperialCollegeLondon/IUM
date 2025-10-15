/-
Copyright (c) 2025 Heather Macbeth, based on prior versions by Marie-Amélie Lawn and Kevin Buzzard.
All rights reserved.
-/
import LectureNotes.Formatting

open Verso.Genre Manual
open Verso.Code.External

set_option verso.exampleProject "../IUM"
set_option verso.exampleModule "IUM.Nat.Addition"
set_option verso.externalExamples.suppressedNamespaces "MyNat"

#doc (Manual) "Definition of addition"  =>

Recall the set-up: $`a` is a fixed natural number,
and we want to define the function which sends $`x` to $`a+x`.
By "That's it", here's what we have to do:

1. Define $`a+0`;
2. If we have already defined $`a+n`, we must define $`a+S(n)`.

We want addition to agree with our real world intuition, so let's make the following definition:

:::definition "add" (title := "Addition")
* Define $`a+0` to be $`a`.
* If $`a+n` is already defined to be $`y`, then define $`a+S(n)` to be $`S(y)`. In other words, $`a+S(n)` is defined to be $`S(a+n)`.
:::

```anchor def_add
def add : ℕ → ℕ → ℕ
  | a, 0 => a
  | a, succ n => succ (add a n)
```

"That's it" ensures that this is a valid definition.
The logic in the successor case is that $`a+S(n)` is $`a` and $`n` and one more, so it's the number after $`a+n`.

Let's now prove that $`1+1=2`.

:::theorem
$`1+1=2`.
:::

:::proof
$$`\begin{align*}
1+1&=1+S(0) &&\mathrm{(by\ definition\ of\ 1)}\\
   &=S(1+0) &&\mathrm{(by\ definition\ of\ }a+S(n))\\
   &=S(1)   &&\mathrm{(by\ definition\ of\ }a+0)\\
   &=2      &&\mathrm{(by\ definition\ of\ }2).
\end{align*}`
:::

*Exercise.* Prove that $`2+2=4`.

-- $$`\begin{align*}
-- 2+2&=2+S(1) \\
--    &=S(2+1)  \\
--    &=S(2+S(0)) \\
--    &=S(S(2+0)) \\
--    &=S(S(2)) \\
--    &=S(3) &&\qquad\star\\
--    &=4.
-- \end{align*}`

Now we have defined addition, the equation $`S(x)=x+1` finally _makes sense_.
Let's prove that it is true.

:::lemma "succ_eq_add_one"
If $`x` is a natural number then $`S(x)=x+1`.
:::

:::proof
$$`\begin{align*}
x+1&=x+S(0)&& \mathrm{(by\ definition\ of\ 1)}\\
&=S(x+0)&& \mathrm{(by\ definition\ of\ }+)\\
&=S(x)&& \mathrm{(by\ definition\ of\ }+).
\end{align*}`
:::
