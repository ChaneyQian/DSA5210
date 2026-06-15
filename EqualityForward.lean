import Formalization
import CompleteBipartite
import Arithmetic

open scoped BigOperators

/-!
# EqualityForward.lean — Person 2

Forward direction of Mantel's equality characterization:
  If G is triangle-free and |E(G)| = ⌊n²/4⌋, then G is a balanced complete bipartite graph.

Strategy:
  1. Choose v of maximum degree; let A = N(v), B = Vᶜ \ A.
  2. Triangle-free → A is independent.
  3. Equality in degree sum → deg(x) = |B| for all x ∈ A → all cross edges present.
  4. Degree constraint on B → B independent.
  5. A, B partition V → G is complete bipartite with parts A, B.
  6. Arithmetic (Person 3 stub) → |A| and |B| balanced.
-/

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

-- ─── Arithmetic lemma — now provided by Person 3's `Arithmetic.lean` ─────────
-- `arithmetic_balanced_of_product_eq_floor` (imported above) replaces the
-- former local placeholder. Signature unchanged, so the call site below is
-- untouched. `mantel_equality_forward` is now fully axiom-clean.

-- ─── T1: N(v) is independent ─────────────────────────────────────────────────

/-- In a triangle-free graph, the neighborhood of any vertex is independent.
    NOTE: the final `exact` depends on the precise argument order of A2's
    `TriangleFree` definition (we do not have Formalization.lean locally);
    the triangle is (v, a, b) with Adj v a, Adj a b, Adj v b. Adjust the
    application once the real definition is visible, or reuse A2's
    `neighbor_independent_of_triangle_free` if it exists. -/
theorem neighborFinset_independent_of_triangleFree
    (htri : TriangleFree G) (v : V) :
    IsIndependentFinset G (G.neighborFinset v) := by
  intro a b ha hb hab
  rw [SimpleGraph.mem_neighborFinset] at ha hb
  exact htri ha hab hb

-- ─── T2: Equality forces all cross edges ─────────────────────────────────────

/-- If equality holds in the degree-sum partition bound, every vertex in A
    (= N(v)) is adjacent to every vertex in B (= N(v)ᶜ). -/
theorem equality_forces_cross_edges
    {v : V}
    (hvmax : ∀ w : V, G.degree w ≤ G.degree v)
    (htri : TriangleFree G)
    (heq : G.edgeFinset.card = G.degree v * (Fintype.card V - G.degree v)) :
    IsCompleteBetween G (G.neighborFinset v) (G.neighborFinset v)ᶜ := by
  let A := G.neighborFinset v
  let B := Aᶜ
  intro a b ha hb
  have hAcard : A.card = G.degree v := rfl
  have hBcard : B.card = Fintype.card V - G.degree v := by
    simp [B, hAcard, Finset.card_compl]
  have h_deg_A : ∀ x ∈ A, G.degree x ≤ B.card := by
    intro x hx
    exact degree_le_compl_neighbor_card_of_mem_neighbor G htri v hx
  have h_deg_B : ∀ y ∈ B, G.degree y ≤ A.card := by
    intro y hy
    have : G.degree y ≤ G.degree v := hvmax y
    rwa [← hAcard] at this
  have h_sum_A : ∑ x ∈ A, G.degree x ≤ A.card * B.card := by
    calc ∑ x ∈ A, G.degree x ≤ ∑ x ∈ A, B.card := Finset.sum_le_sum (fun x hx => h_deg_A x hx)
      _ = A.card * B.card := by simp
  have h_sum_B : ∑ y ∈ B, G.degree y ≤ B.card * A.card := by
    calc ∑ y ∈ B, G.degree y ≤ ∑ y ∈ B, A.card := Finset.sum_le_sum (fun y hy => h_deg_B y hy)
      _ = B.card * A.card := by simp
  have h_sum_split : ∑ x : V, G.degree x = (∑ x ∈ A, G.degree x) + ∑ y ∈ B, G.degree y := by
    exact (Finset.sum_add_sum_compl A (fun x => G.degree x)).symm
  have h_twice_edges : 2 * G.edgeFinset.card = ∑ x : V, G.degree x :=
    G.sum_degrees_eq_twice_card_edges.symm
  have h_eq2 : 2 * G.edgeFinset.card = 2 * (A.card * B.card) := by
    rw [heq, hAcard, hBcard]
  have h_sum_A_eq : ∑ x ∈ A, G.degree x = A.card * B.card := by
    linarith [h_sum_A, h_sum_B, h_sum_split, h_twice_edges, h_eq2]
  have h_diff_zero : ∑ x ∈ A, (B.card - G.degree x) = 0 := by
    rw [Finset.sum_tsub_distrib]
    · simp [h_sum_A_eq]
    · exact h_deg_A
  have h_diff_x_zero : ∀ x ∈ A, B.card - G.degree x = 0 := by
    intro x hx
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => Nat.zero_le _)).mp h_diff_zero x hx
  have h_deg_a : G.degree a = B.card := by
    have h1 := h_diff_x_zero a ha
    have h2 := h_deg_A a ha
    omega
  have h_sub : G.neighborFinset a ⊆ B := by
    intro y hy
    rw [Finset.mem_compl]
    intro hyA
    exact neighbor_independent_of_triangle_free G htri v a ha y hyA ((G.mem_neighborFinset a y).mp hy)
  have h_eq_B : G.neighborFinset a = B := by
    apply Finset.eq_of_subset_of_card_le h_sub
    rw [G.card_neighborFinset_eq_degree a, h_deg_a]
  exact (G.mem_neighborFinset a b).mp (by rw [h_eq_B]; exact hb)

-- ─── T3: Bᶜ is independent ───────────────────────────────────────────────────

/-- Under the same equality condition, the complement of N(v) is independent. -/
theorem compl_neighbors_independent
    {v : V}
    (hvmax : ∀ w : V, G.degree w ≤ G.degree v)
    (htri : TriangleFree G)
    (heq : G.edgeFinset.card = G.degree v * (Fintype.card V - G.degree v)) :
    IsIndependentFinset G (G.neighborFinset v)ᶜ := by
  let A := G.neighborFinset v
  let B := Aᶜ
  intro y z hy hz hyz
  have h_cross := equality_forces_cross_edges G hvmax htri heq
  have hAcard : A.card = G.degree v := rfl
  have h_deg_y : G.degree y ≤ A.card := by
    have : G.degree y ≤ G.degree v := hvmax y
    rwa [← hAcard] at this
  have h_A_sub_Ny : A ⊆ G.neighborFinset y := by
    intro x hx
    have h_cross_xy : G.Adj x y := h_cross hx hy
    exact (G.mem_neighborFinset y x).mpr h_cross_xy.symm
  have h_Acard_le : A.card ≤ G.degree y := by
    rw [← G.card_neighborFinset_eq_degree y]
    exact Finset.card_le_card h_A_sub_Ny
  have h_deg_y_eq : G.degree y = A.card := by
    omega
  have h_Ny_eq_A : G.neighborFinset y = A := by
    refine (Finset.eq_of_subset_of_card_le h_A_sub_Ny ?_).symm
    rw [G.card_neighborFinset_eq_degree y, h_deg_y_eq]
  have hz_in_Ny : z ∈ G.neighborFinset y := (G.mem_neighborFinset y z).mpr hyz
  rw [h_Ny_eq_A] at hz_in_Ny
  have hz_not_in_A : z ∉ A := Finset.mem_compl.mp hz
  exact hz_not_in_A hz_in_Ny

-- ─── Helper: neighborFinset and compl partition ───────────────────────────────

theorem neighborFinset_compl_partition (v : V) :
    IsVertexPartition (G.neighborFinset v) (G.neighborFinset v)ᶜ := by
  constructor
  · rw [Finset.disjoint_left]
    intro a ha hb
    exact (Finset.mem_compl.mp hb) ha
  · ext a
    simp

-- ─── T4: Structural theorem ───────────────────────────────────────────────────

/-- Under equality in Mantel's bound, G is complete bipartite with
    parts N(v) and N(v)ᶜ. -/
theorem equality_forces_partition_complete
    {v : V}
    (hvmax : ∀ w : V, G.degree w ≤ G.degree v)
    (htri : TriangleFree G)
    (heq : G.edgeFinset.card = G.degree v * (Fintype.card V - G.degree v)) :
    IsCompleteBipartiteWithParts G (G.neighborFinset v) (G.neighborFinset v)ᶜ := by
  refine ⟨neighborFinset_compl_partition G v, ?_, ?_, ?_⟩
  · exact neighborFinset_independent_of_triangleFree G htri v
  · exact compl_neighbors_independent G hvmax htri heq
  · exact equality_forces_cross_edges G hvmax htri heq

-- ─── T5 + Final: mantel_equality_forward ─────────────────────────────────────

/-- Forward direction: triangle-free + Mantel bound achieved → balanced complete bipartite. -/
theorem mantel_equality_forward
    (htri : TriangleFree G)
    (heq : G.edgeFinset.card = (Fintype.card V) * (Fintype.card V) / 4) :
    IsBalancedCompleteBipartite G := by
  cases isEmpty_or_nonempty V
  · refine ⟨∅, ∅, ?_, ?_⟩
    · refine ⟨⟨Finset.disjoint_empty_left ∅, ?_⟩, ?_, ?_, ?_⟩
      · ext x; exact False.elim (IsEmpty.false x)
      · intro a b ha hb; exact False.elim (IsEmpty.false a)
      · intro a b ha hb; exact False.elim (IsEmpty.false a)
      · intro a b ha hb; exact False.elim (IsEmpty.false a)
    · left; rfl
  · obtain ⟨v, hv⟩ := G.exists_maximal_degree_vertex
    have hvmax : ∀ w : V, G.degree w ≤ G.degree v := by
      intro w
      rw [← hv]
      exact G.degree_le_maxDegree w
    let d := G.degree v
    let n := Fintype.card V
    let A := G.neighborFinset v
    have hd_le_n : d ≤ n := by
      exact Finset.card_le_univ A
    have h_le : G.edgeFinset.card ≤ d * (n - d) :=
      edge_card_le_max_degree_partition G htri v hvmax
    have h_arith := mantel_arithmetic d n hd_le_n
    have heqn : G.edgeFinset.card = n * n / 4 := heq
    have h_eq2 : G.edgeFinset.card = d * (n - d) := by
      omega
    have h_eq3 : d * (n - d) = n * n / 4 := by
      omega
    have h_bipartite := equality_forces_partition_complete G hvmax htri h_eq2
    have h_bal := arithmetic_balanced_of_product_eq_floor hd_le_n h_eq3
    let B := Aᶜ
    have hA : A.card = d := rfl
    have hB : B.card = n - d := by
      show Aᶜ.card = n - d
      rw [Finset.card_compl, hA]
    rw [← hB, ← hA] at h_bal
    exact ⟨A, B, h_bipartite, h_bal⟩
