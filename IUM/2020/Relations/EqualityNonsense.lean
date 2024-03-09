import Mathbin.Tactic.Default

#align_import «2020».relations.equality_nonsense

variable (α : Type) (x y z : α)

--set_option pp.notation false
example : x = x := by rfl

example : x = y → y = x := by
  intro h
  induction h
  rfl

example : x = y → y = z → x = z := by
  intro hxy
  intro hyz
  induction hxy
  assumption

