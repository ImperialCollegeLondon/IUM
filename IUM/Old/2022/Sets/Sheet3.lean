/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathbin.Tactic.Default

#align_import «2022».sets.sheet3

/-!

# Sets in Lean, example sheet 3 : not in (`∉`)

The definition in Lean of `x ∉ A` is `¬ (x ∈ A)`. In other words,
`x ∉ A`, `¬ (x ∈ A)` and `(x ∈ A) → false` are all equal *by definition*
in Lean. This means that they are all interchangeable, and you can
change between them using the `change` tactic, or you can just keep this
in mind. For example, if you have a hypothesis `h : x ∉ A` and your goal
is `false`, then `apply h` will work and will change the goal to `x ∈ A`.

## Tactics

You can do all these levels just with `intros`, `apply` and `exact`!

-/


-- imports all the Lean tactics
-- imports all the Lean tactics
open Set

variable (X : Type)
  -- Everything will be a subset of `X`
  (A B C D E : Set X)
  -- A,B,C,D,E are subsets of `X`
  (x y z : X)

-- x,y,z are elements of `X` or, more precisely, terms of type `X`
example : x ∉ A → x ∈ A → False := by sorry

example : x ∈ A → x ∉ A → False := by sorry

example : (∀ t, t ∈ A → t ∈ B) → x ∉ B → x ∉ A := by sorry

example : x ∉ (∅ : Set X) := by sorry

