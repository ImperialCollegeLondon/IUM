import Mathbin.Tactic.Default

#align_import «2020».tactic_hints.examples

/-!

# Tactic cheat sheet. 


-- natnumgame tactics

apply, 
exact (and assumption)
split
use (use `use` to make progress with `nonempty X`)



-/


/-!

## 1) Extracting information from hypotheses

-/


/-! 

### 1a) cases and rcases

Many objects in Lean are pairs of data. For example, a proof
of `P ∧ Q` is stored as a pair consisting of a proof of `P` and
a proof of `Q`. The hypothesis `∃ n : ℕ, f n = 37` is stored
internally as a pair, namely a natural `n` and a proof that `f n = 37`.
Note that "hypothesis" and "proof" mean the same thing.

If `h : X` is something which is stored as a pair in Lean,
then `cases h with a b` will destroy `h` and replace it with
the two pieces of data which made up `h`, calling them `a` and `b`.

-/


example (h : ∃ n : ℕ, n ^ 2 = 2) : False :=
  by
  -- h: ∃ (n : ℕ), n ^ 2 = 2
  cases' h with n hn
  -- n: ℕ
  -- hn: n ^ 2 = 2
  sorry

example (P Q : Prop) (h : P ∧ Q) : P :=
  by
  -- h: P ∧ Q
  cases' h with hP hQ
  -- hP: P
  -- hQ: Q
  exact hP

-- Some things are more than two pieces of data! You can do much more
-- elaborate deconstructions with the `rcases` command.
example (R : ℕ → ℕ → Prop) (hR : Equivalence R) : Symmetric R :=
  by
  -- hR: equivalence R
  rcases hR with ⟨hrefl, hsymm, htrans⟩
  -- hrefl: reflexive R
  -- hsymm: symmetric R
  -- htrans: transitive R
  exact hsymm

/-!

## 1b) specialize

Say you have a long hypothesis `h : ∀ n : ℕ, f n > 37 → n = 23`.
This hypothesis is a *function*. It takes as inputs a natural number n
and a proof that `f n > 37`, and then it gives as output a proof
that `n = 23`. You can feed in some inputs and specialize the function.

Say for example you you manage to prove the hypothesis `ht : f t > 37` for some natural
number `t`. Then `specialize h t ft` would change `h` to `t = 23`.

-/


example (X Y : Set ℕ) (a : ℕ) (h : ∀ n : ℕ, n ∈ X → n ∈ Y) (haX : a ∈ X) : a ∈ Y :=
  by
  -- a: ℕ
  -- haX: a ∈ X
  -- h: ∀ (n : ℕ), n ∈ X → n ∈ Y
  specialize h a haX
  -- h: a ∈ Y
  assumption

/-!

# 2) Making new hypothesis

-/


/-!

## have

The `have` tactic makes a new hypothesis. The proof of the current goal
is paused and a new goal is created. Generally one should now put braces
`{ }` because if there is more than one goal then understanding what the
code is doing can get very difficult.

-/


example (a b c n : ℕ) (hn : n > 2) : a ^ n + b ^ n = c ^ n → a * b = 0 :=
  by
  -- ⊢ a ^ n + b ^ n = c ^ n → a * b = 0
  -- looks a bit tricky
  -- why not prove something easier first
  have ha : a + 1 + 1 = a + 2 :=
    by-- ⊢ a + 1 + 1 = a + 2
    apply add_assoc
  -- ha: a + 1 + 1 = a + 2
  -- ⊢ a ^ n + b ^ n = c ^ n → a * b = 0
  sorry

/-!

# 3) Using hypotheses to change the goal.

-/


/-!

## 2a) rw

The generic `sub in` tactic. If `h : X = Y` then `rw h` will change all
`X`'s in the goal to `Y`'s. Also works with `h : P ↔ Q` if `P` and `Q`
are true-false statements. 

-/


example (X Y : Set ℕ) (hXY : X = Y) (a : ℕ) (haX : a ∈ Y) : a ∈ X :=
  by
  -- hXY: X = Y
  -- ⊢ a ∈ X
  rw [hXY]
  -- hXY: X = Y
  -- ⊢ a ∈ Y
  assumption

/-!

## 2b) convert

`convert` is in some sense the opposite way of thinking to `rw`. Instead
of continually rewriting the goal until it becomes one of your assumptions,
why not just tell Lean that the assumption is basically the right answer
modulo a few loose ends, which Lean will then leave for you as new goals.

-/


-- Variants -- `rw h1 at h2`, `rw h1 at h2 ⊢`, `rw h at *`
example (X Y : Set ℕ) (hX : 37 ∈ X) : 37 ∈ Y :=
  by
  -- hX: 37 ∈ X
  -- ⊢ 37 ∈ Y
  convert hX
  -- ⊢ Y = X
  sorry

/-! ### 4a) intro and rintro -/


/-

# 4) Changing the goal without using hypotheses

-/
-- `intro` is a basic tactic for introducing hypotheses
example (P Q : Prop) : P → Q :=
  by
  -- ⊢ P → Q
  intro hP
  -- hP: P
  -- ⊢ Q
  sorry

-- `rintro` is to `intro` what `rcases` is to `cases`. It enables
-- you to assume something and simultaneously take it apart.
example (f : ℕ → ℚ) : (∃ n : ℕ, f n > 37) → ∃ n : ℕ, f n > 36 :=
  by
  -- ⊢ (∃ (n : ℕ), f n > 37) → P
  rintro ⟨n, hn⟩
  --  n: ℕ
  -- hn: f n > 37
  -- ⊢ P
  sorry

/-! ## 4b) ext -/


-- `ext` is Lean's extensionality tactic. If your goal is to prove that 
-- two extensional things are equal (e.g. sets, functions, binary relations)
-- then `ext a` or `ext a b` or whatever is appropriate, will turn the
-- question into the assertion that they behave in the same way. Let's look
-- at some examples
example (A B : Set ℕ) : A = B :=
  by
  -- ⊢ A = B
  ext x
  --  x : ℕ
  -- ⊢ x ∈ A ↔ x ∈ B
  sorry

example (X Y : Type) (f g : X → Y) : f = g :=
  by
  -- ⊢ f = g
  ext x
  --  x : X
  -- ⊢ f x = g x
  sorry

example (α : Type) (R S : α → α → Prop) : R = S :=
  by
  -- ⊢ R = S
  ext a b
  -- a b : α
  -- ⊢ R a b ↔ S a b
  sorry

