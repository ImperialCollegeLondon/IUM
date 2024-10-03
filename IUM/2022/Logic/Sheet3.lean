/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.Tactic

/-!

# Logic in Lean, example sheet 3 : "not" (`¬`)

We learn about how to manipulate `¬ P` in Lean.

# Important : the definition of `¬ P`

In Lean, `¬ P` is *defined* to mean `P → False`. So `¬ P` and `P → False`
are *the same thing* and can be used interchangeably. You can change
from one to the other for free.

## Tactics

You'll need to know about the tactics from the previous sheets,
and also the following tactics:

* `change` (optional)
* `by_contra`
* `by_cases`

### The `change` tactic

The `change` tactic changes a goal to a goal which
is *equal to it by definition*. The example you need to know
is that `¬ P` and `P → False` are equal by definition.

If your goal is `⊢ ¬ P` then `change P → False,` will
change it to `P → False`. Similarly if you have a hypothesis
`h : ¬ P` then `change P → False at h,` will change it to `h : P → False`.

Note that this tactic is just for psychological purposes. If you finish
a proof which uses this tactic, try commenting out the `change` lines
and see if it breaks!

### The `by_contra` tactic

If your goal is `⊢ P` and you want to prove it by contradiction,
`by_contra h,` will change the goal to `False` and add a hypothesis
`h : ¬ P`.

### The `by_cases` tactic

If `P : Prop` is a true-false statement then `by_cases hP : P,`
turns your goal into two goals, one with hypothesis `hP : P`
and the other with hypothesis `hP : ¬ P`.

-/

-- Throughout this sheet, `P`, `Q` and `R` will denote propositions.
variable (P Q R : Prop)

example : ¬P → P → False := by
  sorry

example : ¬True → False := by
  sorry

example : False → ¬True := by
  sorry

example : ¬False → True := by
  sorry

example : True → ¬False := by
  sorry

example : False → ¬P := by
  sorry

example : P → ¬P → False := by
  sorry

example : P → ¬¬P := by
  sorry

example : (P → Q) → ¬Q → ¬P := by
  sorry

example : ¬¬False → False := by
  sorry

example : ¬¬P → P := by
  sorry

example : (¬Q → ¬P) → P → Q := by
  sorry
