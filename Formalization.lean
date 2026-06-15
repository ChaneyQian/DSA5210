import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Tactic

open scoped BigOperators

def TriangleFree {V : Type*} (G : SimpleGraph V) : Prop :=
  ∀ ⦃a b c : V⦄, G.Adj a b → G.Adj b c → G.Adj a c → False

lemma neighbor_independent_of_triangle_free
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (htri : TriangleFree G) (v : V) :
    ∀ a ∈ G.neighborFinset v, ∀ b ∈ G.neighborFinset v, ¬ G.Adj a b := by
  intro a ha b hb hab
  exact htri ((G.mem_neighborFinset v a).mp ha) hab ((G.mem_neighborFinset v b).mp hb)

lemma degree_le_compl_neighbor_card_of_mem_neighbor
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (htri : TriangleFree G) (v : V) {x : V}
    (hx : x ∈ G.neighborFinset v) :
    G.degree x ≤ (G.neighborFinset v)ᶜ.card := by
  rw [← G.card_neighborFinset_eq_degree]
  apply Finset.card_le_card
  intro y hy
  rw [Finset.mem_compl]
  intro hyA
  exact neighbor_independent_of_triangle_free G htri v x hx y hyA
    ((G.mem_neighborFinset x y).mp hy)

lemma edge_card_le_max_degree_partition
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (htri : TriangleFree G)
    (v : V)
    (hmax : ∀ u : V, G.degree u ≤ G.degree v) :
    G.edgeFinset.card ≤
      (G.neighborFinset v).card * (Fintype.card V - (G.neighborFinset v).card) := by
  let A : Finset V := G.neighborFinset v
  have hAcard : A.card = G.degree v := by rfl
  have hBcard : Aᶜ.card = Fintype.card V - A.card := by
    simpa [A] using Finset.card_compl (s := A)
  have hsumA : (∑ x ∈ A, G.degree x) ≤ A.card * Aᶜ.card := by
    calc
      ∑ x ∈ A, G.degree x ≤ ∑ x ∈ A, Aᶜ.card := by
        exact Finset.sum_le_sum fun x hx =>
          degree_le_compl_neighbor_card_of_mem_neighbor G htri v (by simpa [A] using hx)
      _ = A.card * Aᶜ.card := by simp
  have hsumB : (∑ x ∈ Aᶜ, G.degree x) ≤ A.card * Aᶜ.card := by
    calc
      ∑ x ∈ Aᶜ, G.degree x ≤ ∑ x ∈ Aᶜ, A.card := by
        exact Finset.sum_le_sum fun x _ => by
          simpa [A, hAcard] using hmax x
      _ = A.card * Aᶜ.card := by simp [mul_comm]
  have hsplit :
      (∑ x : V, G.degree x) = (∑ x ∈ A, G.degree x) + ∑ x ∈ Aᶜ, G.degree x := by
    simpa [A] using (Finset.sum_add_sum_compl (s := A) (f := fun x : V => G.degree x)).symm
  have htwo :
      2 * G.edgeFinset.card ≤ 2 * (A.card * Aᶜ.card) := by
    rw [← G.sum_degrees_eq_twice_card_edges, hsplit]
    nlinarith
  have hedge : G.edgeFinset.card ≤ A.card * Aᶜ.card := by
    exact Nat.le_of_mul_le_mul_left htwo (by norm_num : 0 < 2)
  simpa [A, hBcard]
    using hedge

lemma mantel_arithmetic_four (d n : ℕ) (hd : d ≤ n) :
    4 * (d * (n - d)) ≤ n * n := by
  have hs : d + (n - d) = n := Nat.add_sub_of_le hd
  nlinarith [sq_nonneg ((d : ℤ) - ((n - d : ℕ) : ℤ))]

lemma mantel_arithmetic (d n : ℕ) (hd : d ≤ n) :
    d * (n - d) ≤ n * n / 4 := by
  rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 4)]
  simpa [mul_comm, mul_left_comm, mul_assoc] using mantel_arithmetic_four d n hd

theorem mantel_bound
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (htri : TriangleFree G) :
    G.edgeFinset.card ≤ (Fintype.card V) * (Fintype.card V) / 4 := by
  cases isEmpty_or_nonempty V
  · have hG : G = ⊥ := by
      ext a b
      constructor
      · intro h
        exact False.elim (IsEmpty.false a)
      · intro h
        cases h
    simp [hG]
  · obtain ⟨v, hv⟩ := G.exists_maximal_degree_vertex
    have hmax : ∀ u : V, G.degree u ≤ G.degree v := by
      intro u
      rw [← hv]
      exact G.degree_le_maxDegree u
    have hpart := edge_card_le_max_degree_partition G htri v hmax
    have hd : (G.neighborFinset v).card ≤ Fintype.card V := Finset.card_le_univ _
    exact hpart.trans (mantel_arithmetic (G.neighborFinset v).card (Fintype.card V) hd)

#print axioms mantel_bound
