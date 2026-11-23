import UnconditionalCounterexample.Variations.DimensionWordDirections
import UnconditionalCounterexample.Variations.DimensionPointJets

/-!
# Simultaneous local coefficient and differential targets
-/

namespace UnconditionalCounterexample.Variations

open MvPolynomial Filter
open scoped Topology

variable {K E σ : Type*} [NontriviallyNormedField K] [NontriviallyNormedField E] [NormedAlgebra K E]

noncomputable def wordLeadingFactor (u : σ → E) (G H : MvPolynomial σ K) (a : ℕ) : E :=
  (a : E) * aeval u G ^ (a-1) / aeval u H

private theorem wordLeadingFactor_ne [CharZero E] (u : σ → E) {G H : MvPolynomial σ K} {a : ℕ}
    (hG : aeval u G ≠ 0) (hH : aeval u H ≠ 0) (ha : 0 < a) : wordLeadingFactor u G H a ≠ 0 :=
  div_ne_zero (mul_ne_zero (Nat.cast_ne_zero.mpr ha.ne') (pow_ne_zero _ hG)) hH

/-- Adding a scaled vanishing polynomial changes each localized word gradient by the
same generator gradient times its explicit scalar. -/
theorem residueWordGradient_add_vanishing (u : σ → E) (G V H : MvPolynomial σ K) (a : ℕ)
    (c : K) (hV : aeval u V = 0) :
    residueWordGradient u (G + C c * V) H a =
      residueWordGradient u G H a +
        (algebraMap K E c * wordLeadingFactor u G H a) • (fun j ↦ aeval u (pderiv j V)) := by
  funext j
  by_cases hH : aeval u H = 0
  · simp [residueWordGradient, wordLeadingFactor, hH]
  · simp [residueWordGradient, wordLeadingFactor, Derivation.leibniz, smul_eq_mul,
      hV, Pi.smul_apply]
    field_simp
    ring

/-- At one stage the same inverse power meets all local coefficient, derivative and scalar
precision requirements. The scalar may be increased after the values and lower correction
polynomial have been chosen. -/
theorem exists_local_target_exponent {ι κ η : Type*} [Finite ι] [Finite κ] [Finite η]
    {L : ι → Type*} [∀ i, NontriviallyNormedField (L i)] [∀ i, NormedAlgebra K (L i)]
    [∀ i, CharZero (L i)] [Fintype σ]
    (π : K) (hπ : π ≠ 0) (hsmall : ‖π‖ < 1) (G V : MvPolynomial σ K)
    (u : ∀ i, σ → L i) (hG : ∀ i, aeval (u i) G ≠ 0) (hV : ∀ i, aeval (u i) V = 0)
    (H : κ → MvPolynomial σ K) (a : κ → ℕ) (ha : ∀ j, 0 < a j)
    (hH : ∀ i j, aeval (u i) (H j) ≠ 0)
    (coeffTest : η → MvPolynomial σ K →ₗ[K] K) (ε : ℝ) (hε : 0 < ε) (N₀ : ℕ) :
    ∃ N ≥ N₀, ∃ F : MvPolynomial σ K, F = G + C (π^N)⁻¹ * V ∧
      (∀ i, aeval (u i) F = aeval (u i) G) ∧
      (∀ l, ‖π^N * coeffTest l F - coeffTest l V‖ < ε) ∧
      ∀ i j, ∃ α : L i, α ≠ 0 ∧ ‖α⁻¹‖ < ε ∧
        ‖α⁻¹ • residueWordGradient (u i) F (H j) (a j) -
          (fun l ↦ aeval (u i) (pderiv l V))‖ < ε := by
  classical
  let w (i : ι) (j : κ) := wordLeadingFactor (u i) G (H j) (a j)
  have hw (i : ι) (j : κ) : w i j ≠ 0 := wordLeadingFactor_ne _ (hG i) (hH i j) (ha j)
  have ht := tendsto_pow_atTop_nhds_zero_of_norm_lt_one hsmall
  have hcoeff (l : η) : ∀ᶠ N : ℕ in atTop, ‖π^N * coeffTest l G‖ < ε := by
    apply Filter.Tendsto.eventually_lt_const hε
    simpa using (ht.mul_const (coeffTest l G)).norm
  have him (i : ι) : Tendsto (fun N : ℕ ↦ algebraMap K (L i) (π^N)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, algebraMapCLM_apply, map_zero] using ((algebraMapCLM K (L i)).continuous.tendsto 0).comp ht
  let c (i : ι) (j : κ) (N : ℕ) := algebraMap K (L i) (π^N) * (w i j)⁻¹
  have hct (i : ι) (j : κ) : Tendsto (c i j) atTop (𝓝 0) := by
    simpa [c] using (him i).mul_const (w i j)⁻¹
  have hsite (i : ι) (j : κ) : ∀ᶠ N : ℕ in atTop, ‖c i j N‖ < ε ∧
      ‖c i j N • residueWordGradient (u i) G (H j) (a j)‖ < ε := by
    apply Filter.Eventually.and
    · apply Filter.Tendsto.eventually_lt_const hε
      simpa using (hct i j).norm
    · apply Filter.Tendsto.eventually_lt_const hε
      simpa using ((hct i j).smul_const (residueWordGradient (u i) G (H j) (a j))).norm
  have hev := (eventually_ge_atTop N₀).and ((eventually_all.mpr hcoeff).and
    (eventually_all.mpr fun i ↦ eventually_all.mpr (hsite i)))
  obtain ⟨N, hn, htests, hsites⟩ := hev.exists
  let F := G + C (π^N)⁻¹ * V
  refine ⟨N, hn, F, rfl, fun i ↦ by simp [F, hV], fun l ↦ ?_, fun i j ↦ ?_⟩
  · have hf : F = G + (π^N)⁻¹ • V := by rw [Algebra.smul_def]; rfl
    rw [hf, map_add, map_smul, smul_eq_mul, mul_add, ← mul_assoc,
      mul_inv_cancel₀ (pow_ne_zero _ hπ), one_mul, add_sub_cancel_right]
    exact htests l
  · let α := algebraMap K (L i) (π^N)⁻¹ * w i j
    have hα : α ≠ 0 := mul_ne_zero ((map_ne_zero _).mpr (inv_ne_zero (pow_ne_zero _ hπ))) (hw i j)
    have hinv : α⁻¹ = c i j N := by simp [α, c, mul_comm]
    refine ⟨α, hα, hinv ▸ (hsites i j).1, ?_⟩
    rw [residueWordGradient_add_vanishing (u i) G V _ _ _ (hV i)]
    change ‖α⁻¹ • (_ + α • _) - _‖ < _
    rw [smul_add, inv_smul_smul₀ hα, add_sub_cancel_right, hinv]
    exact (hsites i j).2

end UnconditionalCounterexample.Variations
