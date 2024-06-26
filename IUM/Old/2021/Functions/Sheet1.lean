/-
Copyright (c) 2021 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathbin.Tactic.Default

#align_import «2021».functions.sheet1

/-!

# Functions in Lean, example sheet 1 : injectivity and surjectivity

In this sheet we'll learn how to manipulate the concepts of 
injectivity and surjectivity in Lean.

The notation for functions is the usual one in matheamtics:
if `X` and `Y` are types, then `f : X → Y` denotes a function
from `X` to `Y`. In fact what is going on here is that `X → Y`
denotes the type of all functions from `X` to `Y`, and `f : X → Y`
means that `f` is a term of type `X → Y`, i.e., a function
from `X` to `Y`.

One thing worth mentioning is that the simplest kind of function
evaluation, where you have `x : X` and `f : X → Y`, doesn't need
brackets: you can just write `f x` instead of `f(x)`. You only
need it when evaluating a function at a more complex object;
for example if we also had `g : Y → Z` then we can't write
`g f x` for `g(f(x))`, we have to write `g(f x)` otherwise
`g` would eat `f` and get confused. Without brackets,
a function just eats the next term greedily.

## Tactics

### More on `rcases` and `rintro` -- the `rfl` hack.

You don't need to know the below trick but it can make your
proofs shorter.

There is a clever hack in Lean which sometimes enables you to
do `cases` and `rw` all in one go. It works like this. Say
your tactic state is

```
h1 : ∃ a, b = f a
h2 : g b = d
⊢ b = c
```

If you do `cases h1 with a ha` or `rcases h1 with ⟨a, ha⟩` (the same thing)
then you'll end up with
```
a : X
ha : b = f a
h2 : g b = d
⊢ b = c
```

Now `ha`, our new hypothesis, is a "formula for b" and probably what you're
going to want to do next is "substitute in for b", i.e. `rw ha,`
or maybe even `rw ha at h2 ⊢,`or `rw ha at *` to replace `b` by `f a`
everywhere. Then there are no `b`s left other than in `ha` itself and
`ha` is now basically redundant.

Instead of the rewrites, you can use the `subst` tactic to do them for you;
`subst ha,` will remove `b` completely, replacing it with `f a` everywhere
and will then delete `ha` for you.

But even better, there is an approach where `ha` is never even created.
The tactic `rcases h1 with ⟨a, rfl⟩`, means "let `b` be `f a` by definition",
i.e. "replace all `b`s with `f a` and delete `b`". It is a bit of a hack
(because it means you can't have a variable called `rfl`) but it's very
convenient for making proofs shorter.

### More on `rw` -- syntactic equality.

The definition of `function.comp`, known to mathematicians via its `∘`
notation, is that `(f ∘ g) x = f (g x)` by definition. So if your
goal mentions `(f ∘ g) x` and you want it to mention `f (g x)` instead,
you can either use the `change` tactic, or you can define `comp_eval`
as I do below, and then `rw comp_eval f g x,`. Or you can just do nothing,
confident in the fact that because `(f ∘ g) x` and `f (g x)` are equal
by definition, we don't have to worry. 

Except here's a case where you have to do something. Say your
tactic state looks like this:

```
h : g x = 37
⊢ (f ∘ g) x = b
```

Then, because `(f ∘ g) x` and `f (g x)` are equal *by definition*,
`rw h,` should work and change the goal to `f 37 = b`, right? Wrong :-(
The `rw` tactic works up to *syntactic equality*. Syntactic equality
is the strongest version of equality -- two terms are syntactically equal
if they are literally the same string of characters. In particular,
`(f ∘ g) x` and `f (g x)` are definitionally equal, but not syntactically
equal, so `rw h,` will fail.

This is why we define `comp_eval` below. It is a proof of `(f ∘ g) x = f (g x)`.
The proof is `refl`, because `refl` works up to definitional equality.
But because we have given the proof a name, you can `rw comp_eval,`
to change `(f ∘ g) x` to `f (g x)`. This means that with the tactic
state above, you can make progress with `rw [comp_eval, h],`.

-/


-- imports all the Lean tactics
-- imports all the Lean tactics
open Function

-- Our functions will go between these sets, or Types as Lean calls them
variable (X Y Z : Type)

-- Let's prove some theorems, each of which are true by definition.
theorem injective_def (f : X → Y) : Injective f ↔ ∀ a b : X, f a = f b → a = b := by rfl

-- this proof works, because `injective f` 
-- means ∀ a b, f a = f b → a = b *by definition*
-- so the proof is "it's reflexivity of `↔`"
-- similarly this is the *definition* of `surjective f`
theorem surjective_def (f : X → Y) : Surjective f ↔ ∀ y : Y, ∃ x : X, f x = y := by rfl

-- similarly the *definition* of `id x` is `x`
theorem id_eval (x : X) : id x = x := by rfl

-- the *definition* of (g ∘ f) (x) is g(f(x)).
theorem comp_eval (f : X → Y) (g : Y → Z) (x : X) : (g ∘ f) x = g (f x) := by rfl

-- Why did we just prove all those theorems with a proof
-- saying "it's true by definition"? Because now, if we want,
-- we can `rw` the theorems to replace things by their definitions.
example : Injective (id : X → X) :=
  by-- you can start with `rw injective_def` if you like
  -- but because `injective_def` is true by definition
  -- you can delete it later :-)
  sorry

example : Surjective (id : X → X) := by sorry

example (f : X → Y) (g : Y → Z) (hf : Injective f) (hg : Injective g) : Injective (g ∘ f) := by
  sorry

example (f : X → Y) (g : Y → Z) (hf : Surjective f) (hg : Surjective g) : Surjective (g ∘ f) := by
  sorry

-- This is a question on the IUM function problem sheet
example (f : X → Y) (g : Y → Z) : Injective (g ∘ f) → Injective f := by sorry

-- This is another one
example (f : X → Y) (g : Y → Z) : Surjective (g ∘ f) → Surjective g := by sorry

