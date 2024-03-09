import Combinatorics.SimpleGraph.Basic
import Mathlib.Algebra.IndicatorFunction

#align_import mathlib.combinatorics.simple_graph.degree

open Finset Nat

open scoped BigOperators

namespace SimpleGraph

variable {α : Type _} [Fintype α] [DecidableEq α] (G : SimpleGraph α) [DecidableRel G.Adj]
  {s t : Finset α} {a : α}

/-- Number of vertices of `s` adjacent to `a`. -/
def degOn (s : Finset α) (a : α) : ℕ :=
  (s ∩ G.neighborFinset a).card

theorem degOn_mono (hst : s ⊆ t) (a : α) : G.degOn s a ≤ G.degOn t a :=
  card_mono <| inter_subset_inter_right hst

@[simp]
theorem degOn_empty (a : α) : G.degOn ∅ a = 0 := by simp [deg_on]

@[simp]
theorem degOn_univ (a : α) : G.degOn univ a = G.degree a := by rw [deg_on, degree, univ_inter]

-- if s and t are disjoint then for any vertex a the deg_on add
theorem degOn_union (h : Disjoint s t) (a) : G.degOn (s ∪ t) a = G.degOn s a + G.degOn t a :=
  by
  unfold deg_on
  rw [← card_disjoint_union, ← inter_distrib_right]
  exact h.mono (inter_subset_left _ _) (inter_subset_left _ _)

-- edges from t to s\t equals edges from s\t to t
theorem sum_degOn_comm (s t : Finset α) : ∑ a in s, G.degOn t a = ∑ a in t, G.degOn s a :=
  by
  simp_rw [deg_on, card_eq_sum_ones, sum_inter_eq_sum_indicator]
  rw [sum_comm]
  simp [Set.indicator_apply, adj_comm]

end SimpleGraph

