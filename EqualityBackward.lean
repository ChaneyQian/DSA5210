import CompleteBipartite
import Arithmetic

open scoped BigOperators

/-!
# EqualityBackward.lean — Person 3

Backward direction of Mantel's equality characterization:
a balanced complete bipartite graph is triangle-free and reaches the Mantel
edge bound.
-/

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- A vertex in the left part of a complete bipartite graph has exactly the
right part as its neighbor finset. -/
lemma complete_bipartite_neighborFinset_eq_right
    {left right : Finset V}
    (h : IsCompleteBipartiteWithParts G left right)
    {a : V} (ha : a ∈ left) :
    G.neighborFinset a = right := by
  ext b
  constructor
  · intro hb
    have hab : G.Adj a b := (G.mem_neighborFinset a b).mp hb
    rcases (complete_bipartite_edges_between h).mp hab with hcross | hcross
    · exact hcross.2
    · exact False.elim ((vertex_partition_not_both h.1) ⟨ha, hcross.1⟩)
  · intro hb
    exact (G.mem_neighborFinset a b).mpr (complete_bipartite_cross_edge h ha hb)

/-- A vertex in the right part of a complete bipartite graph has exactly the
left part as its neighbor finset. -/
lemma complete_bipartite_neighborFinset_eq_left
    {left right : Finset V}
    (h : IsCompleteBipartiteWithParts G left right)
    {b : V} (hb : b ∈ right) :
    G.neighborFinset b = left := by
  ext a
  constructor
  · intro ha
    have hba : G.Adj b a := (G.mem_neighborFinset b a).mp ha
    rcases (complete_bipartite_edges_between h).mp hba with hcross | hcross
    · exact False.elim ((vertex_partition_not_both h.1) ⟨hcross.1, hb⟩)
    · exact hcross.2
  · intro ha
    exact (G.mem_neighborFinset b a).mpr
      (complete_bipartite_cross_edge h ha hb).symm

/-- A complete bipartite graph with specified finite parts has one edge for
each left-right pair. The proof counts degrees and uses the handshaking lemma. -/
theorem complete_bipartite_edge_card
    {left right : Finset V}
    (h : IsCompleteBipartiteWithParts G left right) :
    G.edgeFinset.card = left.card * right.card := by
  have hdeg_left : ∀ x ∈ left, G.degree x = right.card := by
    intro x hx
    rw [← G.card_neighborFinset_eq_degree, complete_bipartite_neighborFinset_eq_right G h hx]
  have hdeg_right : ∀ x ∈ right, G.degree x = left.card := by
    intro x hx
    rw [← G.card_neighborFinset_eq_degree, complete_bipartite_neighborFinset_eq_left G h hx]
  have hsum_left : ∑ x ∈ left, G.degree x = left.card * right.card := by
    calc
      ∑ x ∈ left, G.degree x = ∑ _x ∈ left, right.card := by
        exact Finset.sum_congr rfl hdeg_left
      _ = left.card * right.card := by simp
  have hsum_right : ∑ x ∈ right, G.degree x = right.card * left.card := by
    calc
      ∑ x ∈ right, G.degree x = ∑ _x ∈ right, left.card := by
        exact Finset.sum_congr rfl hdeg_right
      _ = right.card * left.card := by simp
  have hsum_split :
      ∑ x : V, G.degree x =
        (∑ x ∈ left, G.degree x) + ∑ x ∈ right, G.degree x := by
    rw [← Finset.sum_union h.1.1, h.1.2]
  have htwice : 2 * G.edgeFinset.card = 2 * (left.card * right.card) := by
    rw [← G.sum_degrees_eq_twice_card_edges, hsum_split, hsum_left, hsum_right]
    simp [mul_comm, mul_two]
  omega

/-- Backward direction: balanced complete bipartite implies triangle-free and
attains the Mantel edge bound. -/
theorem mantel_equality_backward
    (h : IsBalancedCompleteBipartite G) :
    TriangleFree G ∧
      G.edgeFinset.card = (Fintype.card V) * (Fintype.card V) / 4 := by
  rcases h with ⟨left, right, hcomplete, hbalanced⟩
  have htri : TriangleFree G := complete_bipartite_triangleFree hcomplete
  have hsum : left.card + right.card = Fintype.card V :=
    vertex_partition_card_sum hcomplete.1
  have hedge : G.edgeFinset.card = left.card * right.card :=
    complete_bipartite_edge_card G hcomplete
  have hproduct :
      left.card * right.card = (Fintype.card V) * (Fintype.card V) / 4 :=
    balanced_product_eq_floor hsum hbalanced
  exact ⟨htri, hedge.trans hproduct⟩

#print axioms mantel_equality_backward
