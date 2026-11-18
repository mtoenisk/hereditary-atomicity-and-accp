import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Uniform affine norm growth and small inverse perturbations

The finite-stage scheduler uses a large coefficient to force finitely many
nonconstant affine expressions beyond prescribed norm bounds. The same choice
makes finitely many inverse coefficient perturbations small. These elementary
bounds hold in every normed field; nonzero slopes and positive tolerances are
explicit. Existence of a suitable large coefficient is a separate input.
-/

namespace UnconditionalCounterexample.AffineNormEscape

open scoped BigOperators

variable {K ι : Type*} [NormedField K]

/-- An explicit reverse-triangle threshold for affine norm growth. -/
theorem norm_affine_gt_of_norm_gt (s b c : K) (r : ℝ) (hs : s ≠ 0)
    (hc : (r + ‖b‖) / ‖s‖ < ‖c‖) : r < ‖s * c + b‖ := by
  have hsc : r + ‖b‖ < ‖s * c‖ := by
    rw [norm_mul]
    simpa only [mul_comm] using (div_lt_iff₀ (norm_pos_iff.mpr hs)).mp hc
  have htriangle : ‖s * c‖ ≤ ‖s * c + b‖ + ‖b‖ := by
    simpa only [add_sub_cancel_right] using norm_sub_le (s * c + b) b
  exact lt_of_add_lt_add_right (hsc.trans_le htriangle)

/-- A nonnegative uniform upper bound for a finite family of real thresholds. -/
theorem finite_nonneg_upper_bound (t : Finset ι) (r : ι → ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ i ∈ t, r i ≤ B := by
  refine ⟨∑ i ∈ t, max 0 (r i), Finset.sum_nonneg (fun _ _ => le_max_left _ _), ?_⟩
  intro i hi
  exact (le_max_right 0 (r i)).trans
    (Finset.single_le_sum (fun j _ => le_max_left 0 (r j)) hi)

/-- All nonconstant affine expressions in a finite family eventually exceed
their individual requested norm bounds. -/
theorem exists_bound_norm_affine_gt (t : Finset ι) (s b : ι → K) (r : ι → ℝ)
    (hs : ∀ i ∈ t, s i ≠ 0) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ c : K, B < ‖c‖ → ∀ i ∈ t, r i < ‖s i * c + b i‖ := by
  obtain ⟨B, hB, hbound⟩ := finite_nonneg_upper_bound t (fun i => (r i + ‖b i‖) / ‖s i‖)
  refine ⟨B, hB, ?_⟩
  intro c hc i hi
  exact norm_affine_gt_of_norm_gt (s i) (b i) c (r i) (hs i hi)
    ((hbound i hi).trans_lt hc)

/-- An explicit inverse-coefficient smallness bound. -/
theorem norm_inv_mul_lt_of_norm_gt (c j : K) (ε : ℝ)
    (hε : 0 < ε) (hc : c ≠ 0) (hlarge : ‖j‖ / ε < ‖c‖) :
    ‖c⁻¹ * j‖ < ε := by
  have hbound : ‖j‖ < ε * ‖c‖ := by
    simpa only [mul_comm] using (div_lt_iff₀ hε).mp hlarge
  calc
    ‖c⁻¹ * j‖ = ‖j‖ / ‖c‖ := by rw [norm_mul, norm_inv, div_eq_mul_inv, mul_comm]
    _ < ε := (div_lt_iff₀ (norm_pos_iff.mpr hc)).mpr hbound

/-- A finite family of inverse coefficient perturbations becomes uniformly
small, with a separate positive tolerance for each coefficient. -/
theorem exists_bound_norm_inv_mul_lt (t : Finset ι) (j : ι → K) (ε : ι → ℝ)
    (hε : ∀ i ∈ t, 0 < ε i) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ c : K, B < ‖c‖ → ∀ i ∈ t, ‖c⁻¹ * j i‖ < ε i := by
  obtain ⟨B, hB, hbound⟩ := finite_nonneg_upper_bound t (fun i => ‖j i‖ / ε i)
  refine ⟨B, hB, ?_⟩
  intro c hc i hi
  have hc0 : c ≠ 0 := norm_pos_iff.mp (hB.trans_lt hc)
  exact norm_inv_mul_lt_of_norm_gt c (j i) (ε i) (hε i hi) hc0
    ((hbound i hi).trans_lt hc)

end UnconditionalCounterexample.AffineNormEscape
