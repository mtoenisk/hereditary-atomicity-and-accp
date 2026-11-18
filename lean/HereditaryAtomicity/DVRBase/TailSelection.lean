import HereditaryAtomicity.DVRBase.SourceConstruction
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Analysis.Normed.Group.InfiniteSum

noncomputable section
open scoped BigOperators

namespace HereditaryAtomicity.DVRBase

/-- A nonnegative real sequence with bounded finite partial sums has a tail
on which every finite subsum is small. The tail starts beyond any prescribed
index, and is not replaced by a finite set. -/
theorem exists_tail_finset_sum_lt
    (u : ℕ → ℝ) (hu : ∀ n, 0 ≤ u n) (B : ℝ)
    (hB : ∀ n, ∑ i ∈ Finset.range n, u i ≤ B)
    (ε : ℝ) (hε : 0 < ε) (N₀ : ℕ) :
    ∃ N : ℕ, N₀ ≤ N ∧ ∀ s : Finset ℕ,
      (∀ i ∈ s, N ≤ i) → ∑ i ∈ s, u i < ε := by
  have hsum : Summable u := summable_of_sum_range_le hu hB
  obtain ⟨s, hs⟩ := summable_iff_vanishing_norm.mp hsum ε hε
  let N := max N₀ (s.sup id + 1)
  refine ⟨N, le_max_left _ _, fun t ht => ?_⟩
  have hdisj : Disjoint t s := by
    apply Finset.disjoint_left.mpr
    intro i hit his
    have hi : i ≤ s.sup id := Finset.le_sup (f := id) his
    have hNi := ht i hit
    have hN : s.sup id + 1 ≤ N := le_max_right _ _
    omega
  have hnorm := hs t hdisj
  have hnonneg : 0 ≤ ∑ i ∈ t, u i := Finset.sum_nonneg (fun i _ => hu i)
  simpa only [Real.norm_eq_abs, abs_of_nonneg hnonneg] using hnorm

/-- Every infinite terminal interval of natural indices is cofinal. -/
theorem tail_indices_cofinal (N : ℕ) :
    ∀ m : ℕ, ∃ l, m ≤ l ∧ l ∈ Set.Ici N := by
  intro m
  exact ⟨max m N, le_max_left _ _, show N ≤ max m N from le_max_right _ _⟩

/-- Starting the tail at a positive index excludes the first, zero-indexed
ratio from the selected set. -/
theorem zero_not_mem_tail_indices {N : ℕ} (hN : 1 ≤ N) :
    0 ∉ Set.Ici N := by
  change ¬ N ≤ 0
  omega

namespace SourceBlockData

variable {K : Type*} [Field K] {R : Subring K} (D : SourceBlockData R)

/-- The literal source endpoint identity bounds every finite initial sum
of block weights. -/
theorem sum_range_weight_le (n : ℕ) :
    ∑ i ∈ Finset.range n, D.weight i ≤ (D.exponent : ℝ) - 1 := by
  have heq := D.endpointOrder_eq n
  have hfloor := D.endpoint_order_ge_one n
  change 1 ≤ D.endpointOrder n at hfloor
  rw [Fin.sum_univ_eq_sum_range] at heq
  linarith

/-- A single cofinal tail works uniformly for every finite set of selected
ratio indices. Its doubled weight is less than the first endpoint order. -/
theorem exists_small_weight_tail :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ s : Finset ℕ,
      (∀ i ∈ s, N ≤ i) → 2 * (∑ i ∈ s, D.weight i) < D.endpointOrder 1 := by
  have hpos : 0 < D.endpointOrder 1 :=
    lt_of_lt_of_le zero_lt_one (D.endpoint_order_ge_one 1)
  obtain ⟨N, hN, hsmall⟩ := exists_tail_finset_sum_lt D.weight
    (fun i => (D.ratio_order_pos i).le) ((D.exponent : ℝ) - 1)
    D.sum_range_weight_le (D.endpointOrder 1 / 2) (by positivity) 1
  refine ⟨N, hN, fun s hs => ?_⟩
  have h := hsmall s hs
  linarith

/-- The same chosen infinite tail satisfies the finite Laurent model's
budget at every positive stage, including arbitrary finite subsets of it. -/
theorem exists_tail_all_finite_model_budgets :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ n : ℕ, 0 < n → ∀ s : Finset (Fin n),
      (∀ i ∈ s, N ≤ i.val) →
        2 * (∑ i ∈ s, D.weight i.val) ≤
          remainingValue (fun i : Fin n => D.weight i.val) D.exponent 1 := by
  classical
  obtain ⟨N, hN, hsmall⟩ := D.exists_small_weight_tail
  refine ⟨N, hN, fun n hn s hs => ?_⟩
  have h := hsmall (s.image Fin.val) (by
    rintro j hj
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
    exact hs i hi)
  rw [Finset.sum_image (by
    intro i _ j _ hij
    exact Fin.ext hij)] at h
  rw [← D.endpointOrder_eq_remainingValue n 1 (Nat.succ_le_iff.mpr hn)]
  exact h.le

/-- The selected set is a literal infinite terminal interval. The first
ratio is excluded, cofinality is retained for fresh division, and all finite
stages satisfy the same budget used by the finite obstruction theorem. -/
theorem exists_cofinal_tail_with_model_budget :
    ∃ Λ : Set ℕ, (∃ N : ℕ, 1 ≤ N ∧ Λ = Set.Ici N) ∧
      0 ∉ Λ ∧ (∀ m : ℕ, ∃ l, m ≤ l ∧ l ∈ Λ) ∧
      ∀ n : ℕ, 0 < n → ∀ s : Finset (Fin n),
        (∀ i ∈ s, i.val ∈ Λ) →
          2 * (∑ i ∈ s, D.weight i.val) ≤
            remainingValue (fun i : Fin n => D.weight i.val) D.exponent 1 := by
  obtain ⟨N, hN, hbudget⟩ := D.exists_tail_all_finite_model_budgets
  exact ⟨Set.Ici N, ⟨N, hN, rfl⟩, zero_not_mem_tail_indices hN,
    tail_indices_cofinal N, hbudget⟩

end SourceBlockData
end HereditaryAtomicity.DVRBase
