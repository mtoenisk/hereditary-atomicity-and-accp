import UnconditionalCounterexample.ShiftedEisenstein
import UnconditionalCounterexample.LocalInterpolation
import UnconditionalCounterexample.PadicTargetStability
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.MetricSpace.Pseudo.Pi

/-!
# Stability of the finite local stage conditions

For construction section 3, the fixed-constant monic coefficient family is
continuous under every scalar linear polynomial measurement. This supplies one
positive product of coefficient balls preserving the finitely many required
values, strict word-derivative bounds and transformed coefficient errors.

The p-adic specialization preserves exact normalized-value norms and the actual
q_n return congruence. A degree bound on differences of monic polynomials turns
finitely many coefficient tests into full coefficientwise congruence after each
linear substitution. Choosing rational coefficients in these balls, imposing
Eisenstein/geometric conditions and deriving the final transfer-module estimate
are separate steps.
-/

namespace UnconditionalCounterexample.CoefficientStability

open Polynomial Filter
open scoped Topology

variable {K : Type*} [NontriviallyNormedField K] [CompleteSpace K]

theorem continuous_monicFamily_linear (n : ℕ) (c : K) (L : K[X] →ₗ[K] K) :
    Continuous (fun q : Fin n → K => L (ShiftedEisenstein.monicFamily n c q)) := by
  classical
  have hfin : Continuous (fun q : Fin n → K => (Fin.cases c q : Fin (n + 1) → K)) := by
    apply continuous_pi
    intro j
    refine Fin.cases ?_ (fun i => ?_) j
    · exact continuous_const
    · exact continuous_apply i
  have hlin : Continuous (L.comp (ofFn (n + 1))) :=
    (L.comp (ofFn (n + 1))).continuous_of_finiteDimensional
  apply ((continuous_const (y := L (X ^ (n + 1)))).add (hlin.comp hfin)).congr
  intro q
  simp only [ShiftedEisenstein.monicFamily, map_add, Function.comp_apply,
    Pi.add_apply, LinearMap.comp_apply]

theorem continuous_monicFamily_eval (n : ℕ) (c x : K) :
    Continuous (fun q : Fin n → K => (ShiftedEisenstein.monicFamily n c q).eval x) := by
  simpa using continuous_monicFamily_linear n c (aeval x).toLinearMap

theorem continuous_monicFamily_derivative_eval (n : ℕ) (c x : K) :
    Continuous (fun q : Fin n → K =>
      (ShiftedEisenstein.monicFamily n c q).derivative.eval x) := by
  simpa using continuous_monicFamily_linear n c ((aeval x).toLinearMap.comp derivative)

theorem continuous_monicFamily_wordDerivative
    (n : ℕ) (c x : K) (H : K[X]) (a : ℕ) :
    Continuous (fun q : Fin n → K =>
      LocalInterpolation.wordDerivative (ShiftedEisenstein.monicFamily n c q) H a x) := by
  simp only [LocalInterpolation.wordDerivative, derivative_pow, eval_mul, eval_C, eval_pow]
  exact (((continuous_const.mul ((continuous_monicFamily_eval n c x).pow (a - 1))).mul
    (continuous_monicFamily_derivative_eval n c x)).mul_const _ |>.sub
      ((continuous_monicFamily_eval n c x).pow a |>.mul_const _)).div_const _

theorem continuous_monicFamily_transformedCoeff
    (n : ℕ) (c r : K) (Q : K[X]) (j : ℕ) :
    Continuous (fun q : Fin n → K =>
      (C r * (ShiftedEisenstein.monicFamily n c q).comp Q).coeff j) := by
  have h := continuous_monicFamily_linear n c
    (r • ((lcoeff K j).comp (aeval Q).toLinearMap))
  simpa only [LinearMap.smul_apply, smul_eq_mul, LinearMap.comp_apply,
    lcoeff_apply, AlgHom.toLinearMap_apply, ← comp_eq_aeval, coeff_C_mul] using h

omit [CompleteSpace K] in
theorem exists_coefficient_tolerance_of_mem_nhds
    (n : ℕ) (q : Fin n → K) (U : Set (Fin n → K)) (hU : U ∈ 𝓝 q) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ q' : Fin n → K,
      (∀ j, ‖q' j - q j‖ < ε) → q' ∈ U := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hU
  refine ⟨ε, hε, ?_⟩
  intro q' hq'
  apply hball
  rw [Metric.mem_ball, dist_pi_lt_iff hε]
  intro j
  simpa only [dist_eq_norm] using hq' j

/-- The finite conditions of construction §3 contain a product of coefficient
balls: evaluations stay near their targets, strict word-derivative bounds persist,
and all requested transformed coefficient errors are small. -/
theorem exists_tolerance_values_words_coefficients
    {V W I : Type*} (n : ℕ) (c : K) (q : Fin n → K)
    (tv : Finset V) (xv : V → K) (ev : V → ℝ) (hev : ∀ i ∈ tv, 0 < ev i)
    (tw : Finset W) (xw : W → K) (H : W → K[X]) (a : W → ℕ) (r : W → ℝ)
    (hword : ∀ i ∈ tw,
      r i < ‖LocalInterpolation.wordDerivative (ShiftedEisenstein.monicFamily n c q)
        (H i) (a i) (xw i)‖)
    (tc : Finset I) (scale : I → K) (Q : I → K[X]) (j : I → ℕ)
    (ec : I → ℝ) (hec : ∀ i ∈ tc, 0 < ec i) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ q' : Fin n → K, (∀ k, ‖q' k - q k‖ < ε) →
      (∀ i ∈ tv, ‖(ShiftedEisenstein.monicFamily n c q').eval (xv i) -
        (ShiftedEisenstein.monicFamily n c q).eval (xv i)‖ < ev i) ∧
      (∀ i ∈ tw, r i < ‖LocalInterpolation.wordDerivative
        (ShiftedEisenstein.monicFamily n c q') (H i) (a i) (xw i)‖) ∧
      (∀ i ∈ tc, ‖(C (scale i) *
        (ShiftedEisenstein.monicFamily n c q' -
          ShiftedEisenstein.monicFamily n c q).comp (Q i)).coeff (j i)‖ < ec i) := by
  have hv : ∀ᶠ q' in 𝓝 q, ∀ i ∈ tv,
      ‖(ShiftedEisenstein.monicFamily n c q').eval (xv i) -
        (ShiftedEisenstein.monicFamily n c q).eval (xv i)‖ < ev i := by
    apply (Filter.eventually_all_finset tv).mpr
    intro i hi
    simpa only [dist_eq_norm] using Metric.tendsto_nhds.mp
      (continuous_monicFamily_eval n c (xv i)).continuousAt (ev i) (hev i hi)
  have hw : ∀ᶠ q' in 𝓝 q, ∀ i ∈ tw,
      r i < ‖LocalInterpolation.wordDerivative
        (ShiftedEisenstein.monicFamily n c q') (H i) (a i) (xw i)‖ := by
    apply (Filter.eventually_all_finset tw).mpr
    intro i hi
    exact (isOpen_lt continuous_const
      (continuous_monicFamily_wordDerivative n c (xw i) (H i) (a i)).norm).mem_nhds
        (hword i hi)
  have hc : ∀ᶠ q' in 𝓝 q, ∀ i ∈ tc,
      ‖(C (scale i) * (ShiftedEisenstein.monicFamily n c q' -
        ShiftedEisenstein.monicFamily n c q).comp (Q i)).coeff (j i)‖ < ec i := by
    apply (Filter.eventually_all_finset tc).mpr
    intro i hi
    simpa only [dist_eq_norm, sub_comp, mul_sub, coeff_sub] using Metric.tendsto_nhds.mp
      (continuous_monicFamily_transformedCoeff n c (scale i) (Q i) (j i)).continuousAt
        (ec i) (hec i hi)
  exact exists_coefficient_tolerance_of_mem_nhds n q _ (hv.and (hw.and hc))

end UnconditionalCounterexample.CoefficientStability



namespace UnconditionalCounterexample.CoefficientStability

open Polynomial

variable {p : ℕ} [Fact p.Prime]

/-- At an actual p-adic stage one coefficient ball simultaneously preserves
all numerator norms, refined return bounds, word-derivative bounds, and the
requested integral coefficient errors modulo the specified prime powers. -/
theorem exists_padic_stage_tolerance
    {V W I : Type*} (n : ℕ) (c : ℚ_[p]) (q : Fin n → ℚ_[p])
    (tv : Finset V) (xv B v : V → ℚ_[p]) (ev : V → ℝ)
    (hB : ∀ i ∈ tv, B i ≠ 0) (hv : ∀ i ∈ tv, v i ≠ 0)
    (hev : ∀ i ∈ tv, 0 < ev i)
    (htarget : ∀ i ∈ tv, (ShiftedEisenstein.monicFamily n c q).eval (xv i) = B i * v i)
    (tw : Finset W) (xw : W → ℚ_[p]) (H : W → ℚ_[p][X]) (a : W → ℕ) (r : W → ℝ)
    (hword : ∀ i ∈ tw,
      r i < ‖LocalInterpolation.wordDerivative (ShiftedEisenstein.monicFamily n c q)
        (H i) (a i) (xw i)‖)
    (tc : Finset I) (scale : I → ℚ_[p]) (Q : I → ℚ_[p][X]) (j k : I → ℕ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ q' : Fin n → ℚ_[p], (∀ l, ‖q' l - q l‖ < ε) →
      (∀ i ∈ tv,
        (ShiftedEisenstein.monicFamily n c q').eval (xv i) ≠ 0 ∧
        ‖(ShiftedEisenstein.monicFamily n c q').eval (xv i) / B i‖ = ‖v i‖ ∧
        ‖v i / ((ShiftedEisenstein.monicFamily n c q').eval (xv i) / B i) - 1‖ < ev i) ∧
      (∀ i ∈ tw, r i < ‖LocalInterpolation.wordDerivative
        (ShiftedEisenstein.monicFamily n c q') (H i) (a i) (xw i)‖) ∧
      (∀ i ∈ tc,
        (C (scale i) * (ShiftedEisenstein.monicFamily n c q' -
          ShiftedEisenstein.monicFamily n c q).comp (Q i)).coeff (j i) /
            (p : ℚ_[p]) ^ k i ∈ PadicInt.subring p) := by
  let δ : V → ℝ := fun i => min ‖B i * v i‖ (ev i * ‖B i * v i‖)
  have hδ : ∀ i ∈ tv, 0 < δ i := by
    intro i hi
    have h := norm_pos_iff.mpr (mul_ne_zero (hB i hi) (hv i hi))
    exact lt_min h (mul_pos (hev i hi) h)
  have hp : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  obtain ⟨ε, hε, hclose⟩ := exists_tolerance_values_words_coefficients n c q tv xv δ hδ
    tw xw H a r hword tc scale Q j (fun i => ‖(p : ℚ_[p]) ^ k i‖)
    (fun i _ => norm_pos_iff.mpr (pow_ne_zero _ hp))
  refine ⟨ε, hε, ?_⟩
  intro q' hq'
  obtain ⟨hvalues, hwords, hcoeffs⟩ := hclose q' hq'
  refine ⟨?_, hwords, ?_⟩
  · intro i hi
    apply PadicTargetStability.refined_target_stable_of_norm_sub_lt
      (B i) (v i) _ (ev i) (hB i hi) (hv i hi)
    simpa only [htarget i hi] using hvalues i hi
  · intro i hi
    exact (PadicTargetStability.div_mem_padicInt_iff _ _ (pow_ne_zero _ hp)).mpr
      (hcoeffs i hi).le

end UnconditionalCounterexample.CoefficientStability

namespace UnconditionalCounterexample.CoefficientStability


open Polynomial ShiftedEisenstein

theorem monicFamily_sub_natDegree_le
    {K : Type*} [CommRing K] (n : ℕ) (c : K) (q' q : Fin n → K) :
    (monicFamily n c q' - monicFamily n c q).natDegree ≤ n := by
  classical
  unfold monicFamily
  rw [add_sub_add_left_eq_sub]
  apply (natDegree_sub_le _ _).trans
  exact max_le (Nat.lt_succ_iff.mp (ofFn_natDegree_lt (Nat.succ_pos n) _))
    (Nat.lt_succ_iff.mp (ofFn_natDegree_lt (Nat.succ_pos n) _))

theorem natDegree_C_mul_comp_C_mul_X_le
    {K : Type*} [CommRing K] (f : K[X]) (n : ℕ) (hf : f.natDegree ≤ n)
    (r s : K) : (C r * f.comp (C s * X)).natDegree ≤ n := by
  apply (natDegree_C_mul_le _ _).trans
  apply natDegree_comp_le.trans
  have hs : (C s * X : K[X]).natDegree ≤ 1 :=
    (natDegree_C_mul_le s X).trans natDegree_X_le
  simpa only [mul_one] using Nat.mul_le_mul hf hs

theorem scaled_monicFamily_sub_natDegree_le
    {K : Type*} [CommRing K] (n : ℕ) (c r s : K) (q' q : Fin n → K) :
    (C r * (monicFamily n c q' - monicFamily n c q).comp (C s * X)).natDegree ≤ n :=
  natDegree_C_mul_comp_C_mul_X_le _ n (monicFamily_sub_natDegree_le n c q' q) r s

/-- Finite coefficient tests cover every coefficient once the degree bound
is known; no nonzero condition on the divisor is required. -/
theorem coeff_div_mem_of_fin
    {K : Type*} [Field K] (O : Subring K) (f : K[X]) (n : ℕ)
    (hf : f.natDegree ≤ n) (d : K)
    (h : ∀ j : Fin (n + 1), f.coeff j.val / d ∈ O) :
    ∀ j : ℕ, f.coeff j / d ∈ O := by
  intro j
  by_cases hj : j < n + 1
  · exact h ⟨j, hj⟩
  · rw [coeff_eq_zero_of_natDegree_lt (hf.trans_lt (by omega)), zero_div]
    exact O.zero_mem

theorem scaled_monicFamily_sub_coeff_div_mem_padicInt
    {p : ℕ} [Fact p.Prime] (n : ℕ) (c r s d : ℚ_[p]) (q' q : Fin n → ℚ_[p])
    (h : ∀ j : Fin (n + 1),
      (C r * (monicFamily n c q' - monicFamily n c q).comp (C s * X)).coeff j.val / d
        ∈ PadicInt.subring p) :
    ∀ j : ℕ,
      (C r * (monicFamily n c q' - monicFamily n c q).comp (C s * X)).coeff j / d
        ∈ PadicInt.subring p :=
  coeff_div_mem_of_fin _ _ n (scaled_monicFamily_sub_natDegree_le n c r s q' q) d h


end UnconditionalCounterexample.CoefficientStability

namespace UnconditionalCounterexample.CoefficientStability

open Polynomial

/-- Complete coefficientwise congruences after all specified linear substitutions,
together with return congruences and the other local stage inequalities. -/
theorem exists_padic_stage_tolerance_full
    {p : ℕ} [Fact p.Prime] {V W I : Type*}
    (n : ℕ) (c : ℚ_[p]) (q : Fin n → ℚ_[p])
    (tv : Finset V) (xv B v : V → ℚ_[p]) (kv : V → ℕ)
    (hB : ∀ i ∈ tv, B i ≠ 0) (hv : ∀ i ∈ tv, v i ≠ 0)
    (htarget : ∀ i ∈ tv, (ShiftedEisenstein.monicFamily n c q).eval (xv i) = B i * v i)
    (tw : Finset W) (xw : W → ℚ_[p]) (H : W → ℚ_[p][X]) (a : W → ℕ) (r : W → ℝ)
    (hword : ∀ i ∈ tw,
      r i < ‖LocalInterpolation.wordDerivative (ShiftedEisenstein.monicFamily n c q)
        (H i) (a i) (xw i)‖)
    (tc : Finset I) (scale shift : I → ℚ_[p]) (kc : I → ℕ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ q' : Fin n → ℚ_[p], (∀ l, ‖q' l - q l‖ < ε) →
      (∀ i ∈ tv,
        (ShiftedEisenstein.monicFamily n c q').eval (xv i) ≠ 0 ∧
        ‖(ShiftedEisenstein.monicFamily n c q').eval (xv i) / B i‖ = ‖v i‖ ∧
        (v i / ((ShiftedEisenstein.monicFamily n c q').eval (xv i) / B i) - 1) /
          (p : ℚ_[p]) ^ kv i ∈ PadicInt.subring p) ∧
      (∀ i ∈ tw, r i < ‖LocalInterpolation.wordDerivative
        (ShiftedEisenstein.monicFamily n c q') (H i) (a i) (xw i)‖) ∧
      (∀ i ∈ tc, ∀ j : ℕ,
        (C (scale i) * (ShiftedEisenstein.monicFamily n c q' -
          ShiftedEisenstein.monicFamily n c q).comp (C (shift i) * X)).coeff j /
            (p : ℚ_[p]) ^ kc i ∈ PadicInt.subring p) := by
  classical
  have hp : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  obtain ⟨ε, hε, hclose⟩ := exists_padic_stage_tolerance n c q tv xv B v
    (fun i => ‖(p : ℚ_[p]) ^ kv i‖) hB hv
    (fun i _ => norm_pos_iff.mpr (pow_ne_zero _ hp)) htarget
    tw xw H a r hword (tc.product (Finset.univ : Finset (Fin (n + 1))))
    (fun i => scale i.1) (fun i => C (shift i.1) * X)
    (fun i => i.2.val) (fun i => kc i.1)
  refine ⟨ε, hε, ?_⟩
  intro q' hq'
  obtain ⟨hvalues, hwords, hcoeffs⟩ := hclose q' hq'
  refine ⟨?_, hwords, ?_⟩
  · intro i hi
    obtain ⟨hz, hnorm, hreturn⟩ := hvalues i hi
    exact ⟨hz, hnorm, (PadicTargetStability.div_mem_padicInt_iff _ _
      (pow_ne_zero _ hp)).mpr hreturn.le⟩
  · intro i hi
    apply scaled_monicFamily_sub_coeff_div_mem_padicInt n c (scale i) (shift i)
      ((p : ℚ_[p]) ^ kc i) q' q
    intro j
    exact hcoeffs (i, j) (Finset.mem_product.mpr ⟨hi, Finset.mem_univ j⟩)

end UnconditionalCounterexample.CoefficientStability
