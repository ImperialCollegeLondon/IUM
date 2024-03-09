import Mathbin.Tactic.Default

#align_import «2020».sets.canonical

/- Let α be a fixed ground set, which is a type.

   There is a bijection between
   (a) the type `α → Prop` whose terms
         are functions from `α` to `Prop`, and
   (b) the type `set α`, whose terms
         are subsets of α.
-/
/- Let α be a fixed ground set, which is a type.

   There is a bijection between
   (a) the type `α → Prop` whose terms
         are functions from `α` to `Prop`, and
   (b) the type `set α`, whose terms
         are subsets of α.
-/
def canonical (α : Type) : (α → Prop) ≃ Set α
    where
  toFun -- construction A
  -- let P be a function from α to Prop
  P :=-- Then return the subset {x | P x} of α
    {x : α | P x}
  invFun -- construction B
  -- let X be a subset of α,
  X -- and let's define a function from α to Prop.
  -- So say x is in α,
  a :=-- and we're supposed to be returning a Prop,
      -- so let's return `a ∈ X`
      a ∈
      X
  left_inv := by
    intro P
    ext a
    dsimp
    rfl
  right_inv := by
    intro X
    rfl

