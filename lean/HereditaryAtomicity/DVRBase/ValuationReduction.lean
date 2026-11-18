import HereditaryAtomicity.DVRBase.Reduction
import HereditaryAtomicity.DVRBase.Radical
import HereditaryAtomicity.DVRBase.Chain
import HereditaryAtomicity.NormalizationCenters
import HereditaryAtomicity.ConductorBranches

/-!
# A normalized dominating valuation over a DVR base

Algebraicity over a DVR forces each containing valuation ring to have dimension at
most one. A valuation dominating the local source has a real representative, and
normalization at a specified nonzero nonunit preserves the valuation ring and its
center.
-/

noncomputable section
namespace HereditaryAtomicity.DVRBase
open scoped NNReal

variable {K : Type*} [Field K]

/-- A local domain algebraic over a DVR admits a real valuation with its exact
maximal center, normalized at any specified nonzero source nonunit. -/
theorem exists_normalized_dominating_realValuation_of_algebraic_dvr
    (A R : Subring K) [IsDiscreteValuationRing A] [IsLocalRing R]
    [IsFractionRing R K] [Algebra.IsAlgebraic A K] (hAR : A ≤ R)
    (t : R) (ht0 : t ≠ 0) (ht : t ∈ IsLocalRing.maximalIdeal R) :
    ∃ v : Valuation K ℝ≥0,
      realValuationOrder v (t : K) = 1 ∧
      (∀ r : R, v (r : K) ≤ 1) ∧
      ∀ r : R, r ≠ 0 →
        (0 < realValuationOrder v (r : K) ↔ r ∈ IsLocalRing.maximalIdeal R) := by
  classical
  obtain ⟨W, hRW, hcenter⟩ :=
    exists_valuationSubring_centered_at_maximal R (IsLocalRing.maximalIdeal R)
  have htK : (t : K) ≠ 0 := Subtype.coe_ne_coe.mpr ht0
  have htW : W.valuation (t : K) < 1 := W.mem_nonunits_iff.mp ((hcenter t).mpr ht)
  have hW : W ≠ ⊤ := by
    intro htop
    have hu : IsUnit (⟨(t : K), by simp⟩ : (⊤ : ValuationSubring K)) :=
      (isUnit_iff_ne_zero.mpr htK).map
        (Subring.topEquiv : (⊤ : Subring K) ≃+* K).symm.toRingHom
    rw [htop] at htW
    exact htW.ne ((ValuationSubring.valuation_eq_one_iff ⊤ _).mp hu)
  let : IsFractionRing W.toSubring K := inferInstanceAs (IsFractionRing W K)
  let : Ring.KrullDimLE 1 W :=
    embedded_dimensionLE_one_of_algebraic_dvr A W.toSubring (hAR.trans hRW)
  let : W.valuation.RankOne := Classical.choice (valuationSubring_nonempty_rankOne W hW)
  let w := ValuationApproximation.realValuation W.valuation
  have hequiv : w.IsEquiv W.valuation := ValuationApproximation.realValuation_isEquiv _
  have hwcenter : ∀ r : R, w (r : K) < 1 ↔ r ∈ IsLocalRing.maximalIdeal R := by
    intro r
    have h := hequiv.lt_iff_lt (x := (r : K)) (y := (1 : K))
    simpa only [map_one] using h.trans (W.mem_nonunits_iff.symm.trans (hcenter r))
  have hwt : 0 < realValuationOrder w (t : K) :=
    (realValuationOrder_pos_iff w htK).mpr ((hwcenter t).mpr ht)
  let v := normalizeRealValuation w (t : K) hwt
  refine ⟨v, realValuationOrder_normalize_self w (t : K) hwt, ?_, ?_⟩
  · intro r
    apply (normalizeRealValuation_le_one_iff w (t : K) hwt (r : K)).mpr
    have h : w (r : K) ≤ 1 ↔ W.valuation (r : K) ≤ 1 := by
      simpa only [map_one] using hequiv (r : K) 1
    exact h.mpr (W.valuation_le_one ⟨r, hRW r.property⟩)
  · intro r hr
    exact (realValuationOrder_normalize_pos_iff w (t : K) hwt (r : K)).trans
      ((realValuationOrder_pos_iff w (Subtype.coe_ne_coe.mpr hr)).trans (hwcenter r))

/-- The coefficient uniformizer can be used as the normalization anchor in a
nonfield local domain algebraic over the coefficient DVR. -/
theorem exists_normalized_uniformizer_valuation
    (A R : Subring K) [IsDiscreteValuationRing A] [IsLocalRing R]
    [IsFractionRing R K] [Algebra.IsAlgebraic A K] (hAR : A ≤ R)
    (hfield : ¬ IsField R) (π : A) (hπ : Irreducible π) :
    ∃ v : Valuation K ℝ≥0,
      realValuationOrder v (π : K) = 1 ∧
      (∀ r : R, v (r : K) ≤ 1) ∧
      ∀ r : R, r ≠ 0 →
        (0 < realValuationOrder v (r : K) ↔ r ∈ IsLocalRing.maximalIdeal R) := by
  let : Algebra A R := (Subring.inclusion hAR).toAlgebra
  let : IsScalarTower A R K := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : Algebra.IsAlgebraic A R := Algebra.IsAlgebraic.tower_bot_of_injective
    (A := K) Subtype.val_injective
  have hπR := uniformizer_mem_maximalIdeal (R := R) hπ hfield
  apply exists_normalized_dominating_realValuation_of_algebraic_dvr A R hAR
    (Subring.inclusion hAR π) _ hπR
  exact (map_ne_zero_iff _ (Subring.inclusion_injective hAR)).mpr hπ.ne_zero

/-- The complete valued source-chain reduction for a prescribed nonzero local
chain. Its exact ratios are retained, which is essential for the later
semilocal intersection argument. -/
theorem exists_valued_uniformizerChainData
    (A R : Subring K) [IsDiscreteValuationRing A] [IsLocalRing R]
    [IsFractionRing R K] [Algebra.IsAlgebraic A K] (hAR : A ≤ R)
    (π : A) (hπ : Irreducible π)
    (x t : ℕ → R) (hx : ∀ n, x n ≠ 0)
    (ht : ∀ n, t n ∈ IsLocalRing.maximalIdeal R)
    (hxt : ∀ n, x n = x (n + 1) * t n) :
    ∃ C : UniformizerChainData (Subring.inclusion hAR π) t,
      ∃ v : Valuation K ℝ≥0,
        realValuationOrder v (π : K) = 1 ∧
        (∀ r : R, v (r : K) ≤ 1) ∧
        (∀ r : R, r ≠ 0 →
          (0 < realValuationOrder v (r : K) ↔ r ∈ IsLocalRing.maximalIdeal R)) ∧
        (∀ n, 0 < realValuationOrder v (t n : K)) ∧
        ∀ n, 1 ≤ realValuationOrder v (C.endpoint n : K) := by
  obtain ⟨C, hdiv⟩ := embedded_exists_uniformizerChainData_with_dvd A R hAR hπ x t hx ht hxt
  have hfield : ¬ IsField R := by
    intro hf
    let : Field R := hf.toField
    exact (IsLocalRing.mem_maximalIdeal _).mp (ht 0)
      (isUnit_iff_ne_zero.mpr (C.ratio_ne_zero 0))
  obtain ⟨v, hnorm, hv, hcenter⟩ :=
    exists_normalized_uniformizer_valuation A R hAR hfield π hπ
  refine ⟨C, v, hnorm, hv, hcenter, ?_, ?_⟩
  · intro n
    exact (hcenter (t n) (C.ratio_ne_zero n)).mpr (ht n)
  · intro n
    exact C.one_le_endpoint_order hdiv R.subtype Subtype.val_injective v hv hnorm n

/-- Failure of ACCP over an embedded DVR gives a source chain with power returns and a
normalized dominating real valuation. Ratios have positive order and the normalized
endpoint orders are at least one. -/
theorem exists_valued_uniformizerChainData_of_not_wfDvdMonoid
    (A R : Subring K) [IsDiscreteValuationRing A] [IsLocalRing R]
    [IsFractionRing R K] [Algebra.IsAlgebraic A K] (hAR : A ≤ R)
    (π : A) (hπ : Irreducible π) (hfail : ¬ WfDvdMonoid R) :
    ∃ t : ℕ → R, (∀ n, t n ∈ IsLocalRing.maximalIdeal R) ∧
      ∃ C : UniformizerChainData (Subring.inclusion hAR π) t,
        ∃ v : Valuation K ℝ≥0,
          realValuationOrder v (π : K) = 1 ∧
          (∀ r : R, v (r : K) ≤ 1) ∧
          (∀ r : R, r ≠ 0 →
            (0 < realValuationOrder v (r : K) ↔ r ∈ IsLocalRing.maximalIdeal R)) ∧
          (∀ n, 0 < realValuationOrder v (t n : K)) ∧
          ∀ n, 1 ≤ realValuationOrder v (C.endpoint n : K) := by
  obtain ⟨x, t, hx, ht, hxt⟩ :=
    Factorization.not_wfDvdMonoid_iff_exists_nonunit_chain.mp hfail
  have htM : ∀ n, t n ∈ IsLocalRing.maximalIdeal R :=
    fun n => (IsLocalRing.mem_maximalIdeal _).mpr (ht n)
  exact ⟨t, htM, exists_valued_uniformizerChainData A R hAR π hπ x t hx htM hxt⟩

end HereditaryAtomicity.DVRBase
