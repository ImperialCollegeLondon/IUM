import Combinatorics.SimpleGraph.Basic

#align_import mathlib.combinatorics.simple_graph.basic

/-!
I found dealing with the mathlib "induced" subgraph too painful (probably just too early in my
experience of lean)
-/


open Set

variable {α β V : Type _} {G H : SimpleGraph α} {s t : Set α} {a b : α}

namespace SimpleGraph

@[simp]
theorem disjoint_edgeFinset [Fintype G.edgeSetEmbedding] [Fintype H.edgeSetEmbedding] :
    Disjoint G.edgeFinset H.edgeFinset ↔ Disjoint G H := by
  simp_rw [← Finset.disjoint_coe, coe_edge_finset, disjoint_edge_set]

@[simp]
theorem nonempty_edgeSetEmbedding : G.edgeSetEmbedding.Nonempty ↔ G ≠ ⊥ := by
  rw [Set.nonempty_iff_ne_empty, edge_set_eq_empty.ne]

@[simp]
theorem edgeFinset_eq_empty [Fintype G.edgeSetEmbedding] : G.edgeFinset = ∅ ↔ G = ⊥ := by
  rwa [← edge_finset_bot, edge_finset_inj]

@[simp]
theorem nonempty_edgeFinset [Fintype G.edgeSetEmbedding] : G.edgeFinset.Nonempty ↔ G ≠ ⊥ := by
  rw [Finset.nonempty_iff_ne_empty, edge_finset_eq_empty.ne]

@[simp]
theorem deleteEdges_edgeSetEmbedding (G H : SimpleGraph α) :
    G.deleteEdges H.edgeSetEmbedding = G \ H :=
  rfl

@[simp]
theorem edgeSetEmbedding_top : (⊤ : SimpleGraph V).edgeSetEmbedding = {e : Sym2 V | ¬e.IsDiag} := by
  ext x <;> induction x using Sym2.ind <;> simp

@[simp]
theorem edgeFinset_top [Fintype V] [DecidableEq V] [Fintype (⊤ : SimpleGraph V).edgeSetEmbedding] :
    (⊤ : SimpleGraph V).edgeFinset = Finset.univ.filterₓ fun e => ¬e.IsDiag := by
  ext x <;> induction x using Sym2.ind <;> simp

section Ind

/-- Graph induced by s:finset α, defined to be a simple_graph α (so all vertices outside s have
empty neighborhoods). this is equivalent to  "spanning_coe (induce (s:set α) G)" as we prove below.
-/
def ind (G : SimpleGraph α) (s : Set α) : SimpleGraph α where Adj a b := G.Adj a b ∧ a ∈ s ∧ b ∈ s

@[simp]
theorem adj_ind : (G.ind s).Adj a b ↔ G.Adj a b ∧ a ∈ s ∧ b ∈ s :=
  Iff.rfl

@[simp]
theorem ind_empty (G : SimpleGraph α) : G.ind ∅ = ⊥ := by ext <;> simp

@[simp]
theorem ind_univ (G : SimpleGraph α) : G.ind univ = G := by ext <;> simp

@[simp]
theorem ind_singleton (G : SimpleGraph α) (a : α) : G.ind {a} = ⊥ := by
  ext <;> simp <;> rintro h rfl <;> exact h.ne'

@[simp]
theorem ind_inter (G : SimpleGraph α) (s t : Set α) : G.ind (s ∩ t) = G.ind s ⊓ G.ind t := by
  ext <;> simp <;> tauto

@[simp]
theorem spanningCoe_induce (G : SimpleGraph α) (s : Set α) :
    spanningCoe (induce (s : Set α) G) = G.ind s := by
  ext <;> simp [← and_assoc'] <;> simp_rw [and_assoc', ← and_rotate]

/-- Induced subgraphs on disjoint sets meet in the empty graph. -/
theorem disjoint_ind (h : Disjoint s t) : Disjoint (G.ind s) (G.ind t) := by
  rw [disjoint_iff, ← ind_inter, disjoint_iff_inter_eq_empty.1 h, ind_empty]

end Ind

end SimpleGraph

