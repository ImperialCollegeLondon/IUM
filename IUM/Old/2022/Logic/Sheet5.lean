/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathbin.Tactic.Default

#align_import «2022».logic.sheet5

/-!

# Logic in Lean, example sheet 5 : "iff" (`↔`)

We learn about how to manipulate `P ↔ Q` in Lean.

## Tactics

You'll need to know about the tactics from the previous sheets,
and also the following two new tactics:

* `refl`
* `rw`

### The `refl` tactic

If your goal is `P ↔ P` then `refl,` will solve it.

### The `rw` tactic

If `h : P ↔ Q` is a hypothesis, you can decompose it
using `cases h with hPQ hQP,`. However, if you keep
it around then you can do `rw h,` which changes all `P`s in the goal to `Q`s.
Variant: `rw h at h2,` will change all `P`s to `Q`s in hypothesis `h2`.

-/


-- imports all the Lean tactics
-- imports all the Lean tactics
variable (P Q R S : Prop)

example : P ↔ P := by sorry

example : (P ↔ Q) → (Q ↔ P) := by sorry

example : (P ↔ Q) ↔ (Q ↔ P) := by sorry

example : (P ↔ Q) → (Q ↔ R) → (P ↔ R) := by sorry

example : P ∧ Q ↔ Q ∧ P := by sorry

example : (P ∧ Q) ∧ R ↔ P ∧ Q ∧ R := by sorry

example : P ↔ P ∧ True := by sorry

example : False ↔ P ∧ False := by sorry

example : (P ↔ Q) → (R ↔ S) → (P ∧ R ↔ Q ∧ S) := by sorry

example : ¬(P ↔ ¬P) := by sorry

