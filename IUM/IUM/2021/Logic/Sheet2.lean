/-
Copyright (c) 2021 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathbin.Tactic.Default

#align_import «2021».logic.sheet2

/-!

# Logic in Lean, example sheet 2 : `true` and `false`

We learn about the `true` and `false` propositions.

## Tactics you will need

To solve the levels on this sheet you will need to know all previous
tactics, plus the following two new ones:

* `trivial`
* `exfalso`

### The `trivial` tactic

If your goal is `⊢ true` then `trivial,` will solve it. 

### The `exfalso` tactic

The tactic `exfalso,` turns any goal `⊢ P` into `⊢ false`. 
This is mathematically valid because `false` implies any goal.

-/


-- imports all the Lean tactics
-- imports all the Lean tactics
-- Throughout this sheet, `P`, `Q` and `R` will denote propositions.
variable (P Q R : Prop)

example : True := by sorry

example : True → True := by sorry

example : False → True := by sorry

example : False → False := by sorry

example : (True → False) → False := by sorry

example : False → P := by sorry

example : True → False → True → False → True → False := by sorry

example : P → (P → False) → False := by sorry

example : (P → False) → P → Q := by sorry

example : (True → False) → P := by sorry

