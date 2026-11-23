import UnconditionalCounterexample.Variations.DyadicColumns
import UnconditionalCounterexample.Variations.DyadicProfiles
import Factorization.Bounds
import Mathlib.Tactic.LinearCombination

/-!
# Marked-point weights for the quasi-atomic construction

The zeroth Lean fiber is the first marked fiber and has weight 1/8.
Only the difference of the two marked orders enters the weight.  The full
valuation function on a fiber may be nonzero even when this difference is zero.
-/

noncomputable section
namespace UnconditionalCounterexample.Hierarchy.Weighted

open scoped BigOperators

/-- Weight of the difference of the two marked orders on fiber `n`. -/
def weight (n : ℕ) : ℚ := (1 / 2 : ℚ) ^ (n + 1) / 4

/-- The weighted sum on finitely supported sequences of marked differences. -/
def totalWeight : (ℕ →₀ ℤ) →+ ℚ :=
  (AddMonoidHom.mulLeft (1 / 4 : ℚ)).comp DyadicColumns.mass

@[simp] theorem totalWeight_single (n : ℕ) (z : ℤ) :
    totalWeight (Finsupp.single n z) = (z : ℚ) * weight n := by
  change 1 / 4 * DyadicColumns.mass (Finsupp.single n z) = _
  rw [DyadicColumns.mass_single]
  unfold weight
  ring

theorem totalWeight_first_eight : totalWeight (Finsupp.single 0 8) = 1 := by
  norm_num [weight]

theorem totalWeight_eq_sum (d : ℕ →₀ ℤ) (N : ℕ) (hs : d.support ⊆ Finset.range N) :
    totalWeight d = ∑ i ∈ Finset.range N, (d i : ℚ) * weight i := by
  change 1 / 4 * d.sum (fun i z => z • ((1 / 2 : ℚ) ^ (i + 1))) = _
  rw [Finsupp.sum_of_support_subset _ hs _ (by simp), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _
  simp only [zsmul_eq_mul, weight]
  ring

/-- At a fresh fiber the old weight is an integral multiple of the new
weight. One signed discrepancy there cancels the old prefix exactly. -/
theorem exists_correcting_difference (d : ℕ →₀ ℤ) (N : ℕ)
    (hs : d.support ⊆ Finset.range N) :
    ∃ k : ℤ, totalWeight (d + Finsupp.single N k) = 0 := by
  use -∑ i ∈ Finset.range N, d i * (2 : ℤ) ^ (N - i)
  rw [map_add, totalWeight_single, totalWeight_eq_sum d N hs]
  push_cast
  rw [neg_mul, ← sub_eq_add_neg, Finset.sum_mul]
  apply sub_eq_zero.mpr
  apply Finset.sum_congr rfl
  intro i hi
  have hi' : i ≤ N := (Finset.mem_range.mp hi).le
  have he : N + 1 = (N-i) + (i+1) := by omega
  unfold weight
  rw [he, pow_add (1 / 2 : ℚ) (N-i) (i+1)]
  have hpow : (2 : ℚ)^(N-i) * (1/2 : ℚ)^(N-i) = 1 := by
    rw [← mul_pow]
    norm_num
  linear_combination -(d i : ℚ) * ((1/2 : ℚ)^(i+1) / 4) * hpow

private theorem totalWeight_le_quarter (d : ℕ →₀ ℤ) (hd : ∀ i, d i ≤ 1) :
    totalWeight d ≤ 1/4 := by
  let N := d.support.sup id + 1
  have hs : d.support ⊆ Finset.range N := by
    intro i hi
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.le_sup (f := id) hi))
  have hsum := DyadicProfiles.mass_eq_sum N (fun i => (d i : ℚ)) 0
  have h := DyadicProfiles.mass_le_const N (fun i => (d i : ℚ)) 0 1
    (fun i => by exact_mod_cast hd i) (by norm_num)
  rw [hsum, mul_zero, add_zero] at h
  rw [totalWeight_eq_sum d N hs]
  unfold weight
  simp_rw [← mul_div_assoc, mul_comm (d _ : ℚ)]
  simp_rw [div_eq_mul_inv]
  rw [← Finset.sum_mul]
  apply mul_le_mul_of_nonneg_right _ (by norm_num)
  simpa only [DyadicProfiles.weight, DyadicProfiles.tailWeight, div_eq_mul_inv] using h

/-- Each marked value of an atom lies in {0,1}. The resulting integral
weighted difference must vanish. -/
theorem totalWeight_eq_zero_of_integral (d : ℕ →₀ ℤ)
    (hd : ∀ i, -1 ≤ d i ∧ d i ≤ 1) (hi : ∃ z : ℤ, totalWeight d = z) :
    totalWeight d = 0 := by
  obtain ⟨z, hz⟩ := hi
  have hu := totalWeight_le_quarter d (fun i => (hd i).2)
  have hl := totalWeight_le_quarter (-d) (fun i => by
    simp only [Finsupp.neg_apply]
    linarith [(hd i).1])
  rw [map_neg, hz] at hl
  rw [hz] at hu ⊢
  have hz₁ : (-1 : ℤ) < z := by exact_mod_cast (show (-1 : ℚ) < z by linarith)
  have hz₂ : z < (1 : ℤ) := by exact_mod_cast (show (z : ℚ) < 1 by linarith)
  exact_mod_cast (show z = 0 by omega)

section AtomicProducts

variable {R : Type*} [CommRing R]

/-- Vanishing of the marked weight on atoms extends to all atomic products
and therefore to every quotient of atomic products. -/
theorem weight_eq_zero_of_atomic (W : R → ℚ)
    (hunit : ∀ x, IsUnit x → W x = 0)
    (hmul : ∀ x y, x ≠ 0 → y ≠ 0 → W (x*y) = W x + W y)
    (hatom : ∀ x, Irreducible x → W x = 0)
    {x : R} (hx : x ≠ 0) (ha : Factorization.HasAtomicFactorization x) : W x = 0 := by
  obtain ⟨s, hs, hprod⟩ := ha
  rw [← Factorization.sum_degree_eq_of_associated W hunit hmul hx s hprod]
  exact Multiset.sum_eq_zero (fun a ha => by
    obtain ⟨b, hb, rfl⟩ := Multiset.mem_map.mp ha
    exact hatom b (hs b hb))

end AtomicProducts

end UnconditionalCounterexample.Hierarchy.Weighted
