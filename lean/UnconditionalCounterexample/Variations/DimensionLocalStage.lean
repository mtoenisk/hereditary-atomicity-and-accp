import UnconditionalCounterexample.Variations.DimensionStageNeighborhoods
import UnconditionalCounterexample.Variations.DimensionLocalTargets

namespace UnconditionalCounterexample.Variations

open MvPolynomial Filter
open scoped Topology

private theorem continuous_observe_leading {K σ L : Type*} [NontriviallyNormedField K]
    [Fintype σ] [NormedAddCommGroup L] [NormedSpace K L] (d : ℕ) (leading : MvPolynomial σ K)
    (e : MvPolynomial σ K →ₗ[K] L) : Continuous (fun z ↦ e (leading + polynomialFromBox d z)) := by
  simp_rw [map_add]
  exact continuous_const.add (continuous_observe_box d e)

/-- One processed prime admits a bounded-degree lower target and a whole open
neighborhood enforcing all prescribed value, normalized coefficient, and word-gradient
conditions at its finitely many closed points, for any sufficiently large stage degree. -/
theorem exists_local_stage_neighborhood_uniform {K σ ι : Type*} [NontriviallyNormedField K]
    [Fintype σ] [Finite ι] {E : ι → Type*}
    [∀ i, NontriviallyNormedField (E i)] [∀ i, CharZero (E i)]
    [∀ i, NormedAlgebra K (E i)] [∀ i, FiniteDimensional K (E i)]
    (u : ∀ i, σ → E i) (hgen : ∀ i, Algebra.adjoin K (Set.range (u i)) = ⊤)
    (hdist : Function.Injective (fun i ↦ RingHom.ker (aeval (R := K) (u i)).toRingHom))
    (V : MvPolynomial σ K) (hV : ∀ i, aeval (u i) V = 0)
    (π : K) (hπ : π ≠ 0) (hsmall : ‖π‖ < 1) :
    ∃ b : ℕ, ∀ {κ η : Type*} [Finite κ] [Finite η] (d : ℕ), b < d → ∀ (leading : MvPolynomial σ K) (y : ∀ i, E i),
      (∀ i, y i ≠ 0) → ∀ (S : ∀ i, Set (E i)), (∀ i, S i ∈ 𝓝 (y i)) →
      ∀ (H : κ → MvPolynomial σ K) (a : κ → ℕ), (∀ j, 0 < a j) →
      (∀ i j, aeval (u i) (H j) ≠ 0) →
      ∀ (coeffTest : η → MvPolynomial σ K →ₗ[K] K) (ε : ℝ), 0 < ε → ∀ N₀ : ℕ,
      ∃ N ≥ N₀, ∃ (target : MvPolynomial σ K), target.totalDegree < d ∧
      ∃ (U : Set ((σ →₀ ℕ) → K)), U ∈ 𝓝 (fun m ↦ target.coeff m) ∧
      ∀ q : MvPolynomial σ K, q.totalDegree < d → (fun m ↦ q.coeff m) ∈ U →
        (∀ i, aeval (u i) (leading + q) ∈ S i) ∧
        (∀ l, ‖π^N * coeffTest l (leading + q) - coeffTest l V‖ < ε) ∧
        ∀ i j, ∃ α : E i, α ≠ 0 ∧ ‖α⁻¹‖ < ε ∧
          ‖α⁻¹ • residueWordGradient (u i) (leading + q) (H j) (a j) -
            (fun l ↦ aeval (u i) (pderiv l V))‖ < ε := by
  classical
  obtain ⟨b, hb⟩ := closedPointValues_bounded_correction u hgen hdist
  refine ⟨max b V.totalDegree, ?_⟩
  intro κ η _ _ d hd leading y hy S hS H a ha hH coeffTest ε hε N₀
  obtain ⟨C₀, hC, hval⟩ := hb leading y
  let G := leading + C₀
  obtain ⟨N, hN, F, hF, hv, hc, hg⟩ := exists_local_target_exponent π hπ hsmall G V u
    (fun i ↦ hval i ▸ hy i) hV H a ha hH coeffTest ε hε N₀
  choose α hα hαnorm hdif using hg
  let target := C₀ + C (π^N)⁻¹ * V
  have htarget : target.totalDegree < d := (totalDegree_add _ _).trans_lt (max_lt
    (hC.trans_lt ((le_max_left ..).trans_lt hd)) ((show (C (π^N)⁻¹ * V).totalDegree ≤ V.totalDegree by
      simpa using totalDegree_mul (C (π^N)⁻¹ : MvPolynomial σ K) V).trans_lt
      ((le_max_right ..).trans_lt hd)))
  have heq : leading + target = F := by rw [hF]; exact (add_assoc ..).symm
  let pol (z : (σ →₀ ℕ) → K) := leading + polynomialFromBox d z
  have hpol : pol target.coeff = F := by simpa [pol, polynomialFromBox_coeff target htarget.le] using heq
  have h₁ (i : ι) : ∀ᶠ z in 𝓝 (fun m ↦ target.coeff m), aeval (u i) (pol z) ∈ S i := by
    apply (continuous_observe_leading d leading (aeval (R := K) (u i)).toLinearMap).continuousAt.preimage_mem_nhds
    change S i ∈ 𝓝 (aeval (u i) (pol target.coeff))
    rw [hpol, hv]
    exact hval i ▸ hS i
  have h₂ (l : η) : ∀ᶠ z in 𝓝 (fun m ↦ target.coeff m), ‖π^N * coeffTest l (pol z) - coeffTest l V‖ < ε := by
    apply (isOpen_lt (Continuous.norm ((continuous_const.mul (continuous_observe_leading d leading (coeffTest l))).sub continuous_const))
      continuous_const).mem_nhds
    change ‖π^N * coeffTest l (pol target.coeff) - coeffTest l V‖ < ε
    rw [hpol]
    exact hc l
  have h₃ (i : ι) (j : κ) : ∀ᶠ z in 𝓝 (fun m ↦ target.coeff m),
      ‖(α i j)⁻¹ • residueWordGradient (u i) (pol z) (H j) (a j) -
        (fun l ↦ aeval (u i) (pderiv l V))‖ < ε := by
    apply (isOpen_lt (Continuous.norm (((continuous_wordGradient_box d leading (H j) (u i) (a j)).const_smul
      ((α i j)⁻¹)).sub continuous_const)) continuous_const).mem_nhds
    change ‖(α i j)⁻¹ • residueWordGradient (u i) (pol target.coeff) (H j) (a j) - _‖ < ε
    rw [hpol]
    exact hdif i j
  let U := { z | (∀ i, aeval (u i) (pol z) ∈ S i) ∧
    (∀ l, ‖π^N * coeffTest l (pol z) - coeffTest l V‖ < ε) ∧
    ∀ i j, ‖(α i j)⁻¹ • residueWordGradient (u i) (pol z) (H j) (a j) -
      (fun l ↦ aeval (u i) (pderiv l V))‖ < ε }
  refine ⟨N, hN, target, htarget, U, (eventually_all.mpr h₁).and ((eventually_all.mpr h₂).and
    (eventually_all.mpr fun i ↦ eventually_all.mpr (h₃ i))), ?_⟩
  intro q hq hU
  obtain ⟨h1, h2, h3⟩ := hU
  have hp : pol q.coeff = leading + q := by simp [pol, polynomialFromBox_coeff q hq.le]
  simp only [hp] at h1 h2 h3
  exact ⟨h1, h2, fun i j ↦ ⟨α i j, hα i j, hαnorm i j, h3 i j⟩⟩

/-- One processed prime admits a bounded-degree lower target and a whole open
neighborhood enforcing all prescribed value, normalized coefficient, and word-gradient
conditions at its finitely many closed points, for any sufficiently large stage degree. -/
theorem exists_local_stage_neighborhood {K σ ι κ η : Type*} [NontriviallyNormedField K]
    [Fintype σ] [Finite ι] [Finite κ] [Finite η] {E : ι → Type*}
    [∀ i, NontriviallyNormedField (E i)] [∀ i, CharZero (E i)]
    [∀ i, NormedAlgebra K (E i)] [∀ i, FiniteDimensional K (E i)]
    (u : ∀ i, σ → E i) (hgen : ∀ i, Algebra.adjoin K (Set.range (u i)) = ⊤)
    (hdist : Function.Injective (fun i ↦ RingHom.ker (aeval (R := K) (u i)).toRingHom))
    (V : MvPolynomial σ K) (hV : ∀ i, aeval (u i) V = 0)
    (π : K) (hπ : π ≠ 0) (hsmall : ‖π‖ < 1) :
    ∃ b : ℕ, ∀ (d : ℕ), b < d → ∀ (leading : MvPolynomial σ K) (y : ∀ i, E i),
      (∀ i, y i ≠ 0) → ∀ (S : ∀ i, Set (E i)), (∀ i, S i ∈ 𝓝 (y i)) →
      ∀ (H : κ → MvPolynomial σ K) (a : κ → ℕ), (∀ j, 0 < a j) →
      (∀ i j, aeval (u i) (H j) ≠ 0) →
      ∀ (coeffTest : η → MvPolynomial σ K →ₗ[K] K) (ε : ℝ), 0 < ε → ∀ N₀ : ℕ,
      ∃ N ≥ N₀, ∃ (target : MvPolynomial σ K), target.totalDegree < d ∧
      ∃ (U : Set ((σ →₀ ℕ) → K)), U ∈ 𝓝 (fun m ↦ target.coeff m) ∧
      ∀ q : MvPolynomial σ K, q.totalDegree < d → (fun m ↦ q.coeff m) ∈ U →
        (∀ i, aeval (u i) (leading + q) ∈ S i) ∧
        (∀ l, ‖π^N * coeffTest l (leading + q) - coeffTest l V‖ < ε) ∧
        ∀ i j, ∃ α : E i, α ≠ 0 ∧ ‖α⁻¹‖ < ε ∧
          ‖α⁻¹ • residueWordGradient (u i) (leading + q) (H j) (a j) -
            (fun l ↦ aeval (u i) (pderiv l V))‖ < ε := by
  obtain ⟨b, hb⟩ := exists_local_stage_neighborhood_uniform u hgen hdist V hV π hπ hsmall
  exact ⟨b, hb⟩

end UnconditionalCounterexample.Variations
