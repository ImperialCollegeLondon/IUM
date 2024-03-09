import Mathbin.Tactic.Default

#align_import «2020».logic.bool_not

inductive Bool2
  | ff2 : Bool2
  | tt2 : Bool2
  deriving Fintype

namespace Bool2

def and2 : Bool2 → Bool2 → Bool2
  | ff2, P => ff2
  | tt2, P => P

def or2 : Bool2 → Bool2 → Bool2
  | tt2, P => tt2
  | ff2, P => P

def not2 : Bool2 → Bool2
  | tt2 => ff2
  | ff2 => tt2

def xor2 (x y : Bool2) :=
  and2 (or2 x y) (not2 (and2 x y))

def going : Bool2 → Bool
  | ff2 => true
  | tt2 => false

end Bool2

open Bool2

def Bool.to2 : Bool → Bool2
  | tt => ff2
  | ff => tt2

namespace Bool2

-- no good -- false and true name clash
-- `bool2.F`, standing for "From `bool` (to `bool2` in this case)".
-- `bool2.T`, standing for "To `bool` (from `bool2` in this case)"
-- So anything we can do in `bool` about `bool2` 
-- These functions bijectively identify `bool` and `bool2`.
open Bool

def equiv : Bool2 ≃ Bool where
  toFun := going
  invFun := to2
  left_inv := by
    intro x
    cases x <;> rfl
  right_inv := by rintro (ht | hf) <;> rfl

end Bool2

-- every definition involving bool has a corresponding definition
-- in bool2
-- What construction in `bool2` corresponds to `and` in `bool`?
example (x y : Bool) : (x && y).to2 = or2 x.to2 y.to2 := by cases x <;> cases y <;> rfl

example (x y : Bool) : (x || y).to2 = and2 x.to2 y.to2 := by cases x <;> cases y <;> rfl

example (x y : Bool) : (xor x y).to2 = not2 (xor2 x.to2 y.to2) := by cases x <;> cases y <;> rfl

/- ./././Mathport/Syntax/Translate/Command.lean:739:23: unsupported: advanced #print -/
--  sorry,sorry,sorry,sorry,
example (x : Bool) : (not x).to2 = not2 x.to2 := by cases x <;> rfl

def bimp : Bool → Bool → Bool
  | ff, tt => false
  | _, _ => true

-- corresponds to something awful
-- Computer scientists don't want to reason about bool
-- or prove theorems about it -- they just need it
-- to make data structures, recording yes-no answers
-- to questions about the terms involved.
example (b : Bool) : b = false ∨ b = true :=
  Bool.dichotomy b

-- I can'y do this -- ask Chris?
example :
    ∀ f : Bool → Bool → Bool,
      (∀ x y : Bool, f x y = f y x) →
        f = or ∨
          f = and ∨
            f = xor ∨
              f = fun x y =>
                not (and x y) ∨
                  f = fun x y =>
                    not (or x y) ∨
                      f = fun x y => not (xor x y) ∨ f = fun x y => true ∨ f = fun x y => false :=
  by
  intros
  rw [Function.funext_iff]
  rw [Function.funext_iff]
  rw [Function.funext_iff]
  rw [Function.funext_iff]
  cases (f tt tt).dichotomy <;> cases (f tt ff).dichotomy <;> cases (f ff tt).dichotomy <;>
    cases (f ff ff).dichotomy
  · sorry
  repeat' sorry

--  exact dec_trivial,
-- now let's see forall and exists
variable (Ω : Type) (X Y : Set Ω)

example : (¬∃ a, X a) ↔ ∀ b, ¬X b := by
  constructor
  · intro h
    intro b hb
    apply h
    use b
    assumption
  · intro h
    intro h2
    cases' h2 with a ha
    apply h a
    assumption

example : (¬∀ a, X a) ↔ ∃ b, ¬X b := by
  constructor
  · -- classical
    intro h
    classical
    by_contra hnX
    apply h
    intro a
    by_contra hXa
    apply hnX
    use a
  · intro h
    cases' h with b hb
    intro h
    apply hb
    apply h

example : (¬∃ a, X a) ↔ ∀ b, ¬X b := by
  constructor
  · intro h
    intro b hb
    apply h
    use b
    assumption
  · intro h
    intro h2
    cases' h2 with a ha
    apply h a
    assumption

