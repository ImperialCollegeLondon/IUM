import Data.Real.Ennreal

#align_import «2020».sets.real_numbers

-- We define real numbers using decimals (base 10).
-- We define real numbers using decimals (base 10).
/-- The non-negative real numbers in the mind of a schoolkid -/
structure Mynnreal : Type where
  -- An auxiliary non-negative real number $x$ has an
  -- "integer part", its `floor`...
  floor : ℕ
  -- ...and the decimal part, an infinite string of digits
  frac : ℕ → Fin 10
  -- assuming base 10, so digits={0,1,...,9}
  -- except that you're not allowed to end in infinitely many nines
  no_nines : ∀ B : ℕ, ∃ N : ℕ, B ≤ N ∧ frac N ≠ 9

namespace Mynnreal

def toReal (x : Mynnreal) : ℝ :=
  x.floor + 0

--infinite sums?
-- see thread "infinite sums of reals" on Zulip
end Mynnreal

