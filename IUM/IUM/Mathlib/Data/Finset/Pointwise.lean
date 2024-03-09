import Data.Finset.Pointwise

#align_import mathlib.data.finset.pointwise

open MulOpposite

open scoped Pointwise

variable {α : Type _}

namespace Finset

section One

variable [One α] {s : Finset α}

@[simp, norm_cast, to_additive]
theorem coe_eq_one : (s : Set α) = 1 ↔ s = 1 :=
  coe_eq_singleton

end One

section Mul

variable [DecidableEq α] [Mul α]

@[simp, to_additive]
theorem singleton_mul' (a : α) (s : Finset α) : {a} * s = a • s :=
  singleton_mul _

@[simp, to_additive]
theorem hMul_singleton' (s : Finset α) (a : α) : s * {a} = op a • s :=
  mul_singleton _

end Mul

end Finset

