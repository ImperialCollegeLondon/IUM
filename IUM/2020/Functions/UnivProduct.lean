import Mathbin.Tactic.Default

#align_import «2020».functions.univ_product

-- notation for products
-- notation for products
-- enter the product namespace
-- enter the product namespace
namespace Prod

variable (X Y : Type)

-- Notation for product is `×`, `\times` in VS Code
#check X × Y

-- Type. 
-- notation for elements
variable (x : X) (y : Y)

/-! ## The Data -/


-- this is notation for `prod.mk`, the function which constructs
-- an element of X × Y from an element of `X` and an eleent of `Y`
#check (x, y)

-- X × Y
-- The projections are called `fst` and `snd`.
#check Prod.fst

#check Prod.snd

-- but "dot notation" `a.1` and `a.2` are used more often if `a : X × Y`
-- The
#check Prod

--#print prefix prod
#check @mk

/-! ## The proofs that it satisfies the axioms for product -/


-- this one is true by definition but actually
-- using definitional equality is in some
-- sense cheating the system
example : (x, y).1 = x := by rfl

-- this one is true by something
example (a : X × Y) : (a.1, a.2) = a := by apply mk.eta

/-! ## the universal property -/


-- this axiom is called "eta conversion"
#check @Prod.rec

-- universal property
example :
    ∀ (T : Type) (f : T → X) (g : T → Y), ∃! h : T → X × Y, Prod.fst ∘ h = f ∧ Prod.snd ∘ h = g :=
  by
  intros
  use fun t => (f t, g t)
  -- tidy works now
  constructor
  constructor
  rfl
  rfl
  rintro j ⟨rfl, rfl⟩
  funext t
  apply mk.eta.symm

end Prod

