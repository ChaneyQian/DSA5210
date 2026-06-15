import Formalization

open scoped BigOperators

/-- A finite vertex set is independent if no two vertices in it are adjacent. -/
def IsIndependentFinset {V : Type*} (G : SimpleGraph V) (s : Finset V) : Prop :=
  ∀ ⦃a b : V⦄, a ∈ s → b ∈ s → ¬ G.Adj a b

/-- Every vertex on the left is adjacent to every vertex on the right. -/
def IsCompleteBetween {V : Type*} (G : SimpleGraph V) (left right : Finset V) : Prop :=
  ∀ ⦃a b : V⦄, a ∈ left → b ∈ right → G.Adj a b

/-- Two finite sets form a partition of the whole vertex type. -/
def IsVertexPartition {V : Type*} [Fintype V] [DecidableEq V] (left right : Finset V) : Prop :=
  Disjoint left right ∧ left ∪ right = Finset.univ

/-- A graph is complete bipartite with the given finite left and right parts. -/
def IsCompleteBipartiteWithParts {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (left right : Finset V) : Prop :=
  IsVertexPartition left right ∧
    IsIndependentFinset G left ∧
    IsIndependentFinset G right ∧
    IsCompleteBetween G left right

/-- The two parts are balanced: their sizes differ by at most one. -/
def IsBalancedParts {V : Type*} (left right : Finset V) : Prop :=
  left.card = right.card ∨ left.card + 1 = right.card ∨ right.card + 1 = left.card

/-- A graph is a balanced complete bipartite graph for some finite partition. -/
def IsBalancedCompleteBipartite {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) : Prop :=
  ∃ left right : Finset V,
    IsCompleteBipartiteWithParts G left right ∧ IsBalancedParts left right

lemma vertex_partition_card_sum {V : Type*} [Fintype V] [DecidableEq V]
    {left right : Finset V} (hpart : IsVertexPartition left right) :
    left.card + right.card = Fintype.card V := by
  rw [← Finset.card_union_of_disjoint hpart.1, hpart.2, Finset.card_univ]

lemma complete_bipartite_no_edge_inside_left {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {left right : Finset V}
    (h : IsCompleteBipartiteWithParts G left right)
    {a b : V} (ha : a ∈ left) (hb : b ∈ left) :
    ¬ G.Adj a b :=
  h.2.1 ha hb

lemma complete_bipartite_no_edge_inside_right {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {left right : Finset V}
    (h : IsCompleteBipartiteWithParts G left right)
    {a b : V} (ha : a ∈ right) (hb : b ∈ right) :
    ¬ G.Adj a b :=
  h.2.2.1 ha hb

lemma complete_bipartite_cross_edge {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {left right : Finset V}
    (h : IsCompleteBipartiteWithParts G left right)
    {a b : V} (ha : a ∈ left) (hb : b ∈ right) :
    G.Adj a b :=
  h.2.2.2 ha hb

lemma vertex_partition_left_or_right {V : Type*} [Fintype V] [DecidableEq V]
    {left right : Finset V} (hpart : IsVertexPartition left right) (v : V) :
    v ∈ left ∨ v ∈ right := by
  have hv : v ∈ left ∪ right := by
    rw [hpart.2]
    exact Finset.mem_univ v
  exact Finset.mem_union.mp hv

lemma vertex_partition_not_both {V : Type*} [Fintype V] [DecidableEq V]
    {left right : Finset V} (hpart : IsVertexPartition left right) {v : V} :
    ¬ (v ∈ left ∧ v ∈ right) := by
  intro hv
  exact Finset.disjoint_left.mp hpart.1 hv.1 hv.2

lemma complete_bipartite_edges_between {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {left right : Finset V}
    (h : IsCompleteBipartiteWithParts G left right) {a b : V} :
    G.Adj a b ↔ (a ∈ left ∧ b ∈ right) ∨ (a ∈ right ∧ b ∈ left) := by
  constructor
  · intro hab
    rcases vertex_partition_left_or_right h.1 a with ha_left | ha_right
    · rcases vertex_partition_left_or_right h.1 b with hb_left | hb_right
      · exact False.elim (complete_bipartite_no_edge_inside_left h ha_left hb_left hab)
      · exact Or.inl ⟨ha_left, hb_right⟩
    · rcases vertex_partition_left_or_right h.1 b with hb_left | hb_right
      · exact Or.inr ⟨ha_right, hb_left⟩
      · exact False.elim (complete_bipartite_no_edge_inside_right h ha_right hb_right hab)
  · intro hcross
    rcases hcross with ⟨ha_left, hb_right⟩ | ⟨ha_right, hb_left⟩
    · exact complete_bipartite_cross_edge h ha_left hb_right
    · exact (complete_bipartite_cross_edge h hb_left ha_right).symm

lemma complete_bipartite_triangleFree {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {left right : Finset V}
    (h : IsCompleteBipartiteWithParts G left right) :
    TriangleFree G := by
  intro a b c hab hbc hac
  have hab_cross := (complete_bipartite_edges_between h).mp hab
  have hbc_cross := (complete_bipartite_edges_between h).mp hbc
  rcases hab_cross with ⟨ha_left, hb_right⟩ | ⟨ha_right, hb_left⟩
  · rcases hbc_cross with ⟨hb_left, hc_right⟩ | ⟨_hb_right, hc_left⟩
    · exact (vertex_partition_not_both h.1) ⟨hb_left, hb_right⟩
    · exact complete_bipartite_no_edge_inside_left h ha_left hc_left hac
  · rcases hbc_cross with ⟨_hb_left, hc_right⟩ | ⟨hb_right, hc_left⟩
    · exact complete_bipartite_no_edge_inside_right h ha_right hc_right hac
    · exact (vertex_partition_not_both h.1) ⟨hb_left, hb_right⟩
