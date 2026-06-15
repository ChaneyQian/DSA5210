import Mathlib.Tactic

/-!
# Arithmetic.lean — Person 3

Elementary natural-number arithmetic for the equality case of Mantel's theorem.
The balanced conclusion uses the exact three-way disjunction chosen by
`IsBalancedParts` in `CompleteBipartite.lean`.
-/

/-- If `d * (n - d)` reaches `⌊n² / 4⌋`, the two factors differ by at most one. -/
theorem arithmetic_balanced_of_product_eq_floor {n d : ℕ} (hd : d ≤ n)
    (heq : d * (n - d) = n * n / 4) :
    d = n - d ∨ d + 1 = n - d ∨ (n - d) + 1 = d := by
  have hsum : d + (n - d) = n := Nat.add_sub_of_le hd
  have hmod_lt : (n * n) % 4 < 4 := Nat.mod_lt _ (by norm_num)
  have hdivmod : (n * n) % 4 + 4 * (n * n / 4) = n * n := by
    omega
  have hfloor_upper : n * n < 4 * (n * n / 4 + 1) := by
    omega
  by_contra hbal
  have hunbalanced : d + 2 ≤ n - d ∨ (n - d) + 2 ≤ d := by
    omega
  rcases hunbalanced with hleft | hright
  · have hsub : ((n - d) - d) + d = n - d := Nat.sub_add_cancel (by omega)
    have hsquare : 4 ≤ ((n - d) - d) ^ 2 := by
      have : 2 ≤ (n - d) - d := by omega
      nlinarith
    have hidentity :
        n * n = 4 * (d * (n - d)) + ((n - d) - d) ^ 2 := by
      nlinarith
    omega
  · have hsub : (d - (n - d)) + (n - d) = d := Nat.sub_add_cancel (by omega)
    have hsquare : 4 ≤ (d - (n - d)) ^ 2 := by
      have : 2 ≤ d - (n - d) := by omega
      nlinarith
    have hidentity :
        n * n = 4 * (d * (n - d)) + (d - (n - d)) ^ 2 := by
      nlinarith
    omega

/-- Balanced nonnegative factors with sum `n` have product `⌊n² / 4⌋`. -/
theorem balanced_product_eq_floor {a b n : ℕ}
    (hsum : a + b = n)
    (hbal : a = b ∨ a + 1 = b ∨ b + 1 = a) :
    a * b = n * n / 4 := by
  rcases hbal with hab | hab | hab
  · subst b
    have hfour : n * n = 4 * (a * a) := by nlinarith
    rw [hfour]
    omega
  · have hfour : n * n = 4 * (a * b) + 1 := by nlinarith
    rw [hfour]
    omega
  · have hfour : n * n = 4 * (a * b) + 1 := by nlinarith
    rw [hfour]
    omega
