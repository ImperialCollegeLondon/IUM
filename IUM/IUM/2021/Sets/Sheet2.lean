/-
Copyright (c) 2021 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathbin.Tactic.Default

#align_import «2021».sets.sheet2

/-!

# Sets in Lean, example sheet 2 : the empty set and the "universal set".

We know what the empty subset of `X` is, and the Lean notation for
it is `∅`, or, if you want to say which type we're the empty subset
of, it's `∅ : set X`. 

At the other extreme, the subset of `X` containing all the terms of type `X`
is...well...mathematicians would just call it `X`, but `X` is a type, and
so if we want a set it's called `set.univ : set X`, or just `univ : set X` if
we have opened the `set` namespace. Let's do that now.

-/


-- imports all the Lean tactics
-- imports all the Lean tactics
open Set

/-

## Important

`x ∈ ∅` is *by definition* equal to `false` and `x ∈ univ` is *by definition*
equal to `true`. You can use the `change` tactic to make these changes
if you like. But you don't have to.

## Tactics you will need

You've seen them already. `trivial` proves `⊢ true` and `exfalso`
changes `⊢ P` to `⊢ false`.

-/
-- set up variables
variable (X : Type)
  -- Everything will be a subset of `X`
  (A B C D E : Set X)
  -- A,B,C,D,E are subsets of `X`
  (x y z : X)

-- x,y,z are elements of `X` or, more precisely, terms of type `X`
/-

If `x : X` then `x ∈ ∅` is *by definition* `false`, and `x ∈ univ` is
*by definition* `true`. So you can use the `change` tactic to change
between these things, for example if your goal is

```
⊢ x ∈ univ
```

then `change true` will change the goal to

```
⊢ true
```

and you can now prove this goal with `trivial`. However you can prove
it with `trivial` even without `change`ing it.

-/
open Set

example : x ∈ (univ : Set X) := by sorry

example : x ∈ (∅ : Set X) → False := by sorry

example : ∀ x : X, x ∈ A → x ∈ (univ : Set X) := by sorry

example : ∀ x : X, x ∈ (∅ : Set X) → x ∈ A := by sorry

