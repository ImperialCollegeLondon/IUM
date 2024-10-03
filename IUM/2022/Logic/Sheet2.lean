/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.Tactic

/-!

# Logic in Lean, example sheet 2 : `True` and `False`

We learn about the `True` and `False` propositions.

## Tactics you will need

To solve the levels on this sheet you will need to know all previous
tactics, plus the following two new ones:

* `trivial`
* `exfalso`

### The `trivial` tactic

If your goal is `⊢ True` then `trivial,` will solve it.

### The `exfalso` tactic

The tactic `exfalso,` turns any goal `⊢ P` into `⊢ False`.
This is mathematically valid because `False` implies any goal.

-/

-- Throughout this sheet, `P`, `Q` and `R` will denote propositions.
variable (P Q R : Prop)

example : True := by
  sorry

example : True → True := by
  sorry

example : False → True := by
  sorry

example : False → False := by
  sorry

example : (True → False) → False := by
  sorry

example : False → P := by
  sorry

example : True → False → True → False → True → False := by
  sorry

example : P → (P → False) → False := by
  sorry

example : (P → False) → P → Q := by
  sorry

example : (True → False) → P := by
  sorry
