import HereditaryAtomicity.DVRBase.SourceCertificate
import HereditaryAtomicity.DVRBase.ValuationReduction

/-!
# Standalone local chain certificates

The coefficient and ambient completions are constructed from the normalized
real valuation. The local conclusion concerns the literal source subring, with
its original DVR coefficients and selected blocks of the prescribed chain.
No hereditary atomicity or semilocal hypothesis is used.
-/

noncomputable section
namespace HereditaryAtomicity.DVRBase
open scoped NNReal

variable {K : Type*} [Field K]

/-- Complete the normalized algebraic DVR data and construct one block sequence
whose certificate works for every admissible tail. The source need not be
contained in the valuation ring: only the original coefficient DVR is bounded,
and the given endpoints have order at least one. All completion fields, maps,
and valuation/norm compatibilities are constructed inside the proof. -/
theorem UniformizerChainData.exists_completed_source_certificate
    (O R : Subring K) [IsDiscreteValuationRing O] [Algebra.IsAlgebraic O K]
    (hOR : O ≤ R) (π : O) (hπ : Irreducible π) {t : ℕ → R}
    (C : UniformizerChainData (Subring.inclusion hOR π) t)
    (w : Valuation K ℝ≥0) (hO : ∀ a : O, w (a : K) ≤ 1)
    (hnorm : realValuationOrder w (π : K) = 1)
    (ht : ∀ n, 0 < realValuationOrder w (t n : K))
    (hc : ∀ n, 1 ≤ realValuationOrder w (C.endpoint n : K)) :
    ∃ (D : SourceBlockData R) (a l : ℕ → ℕ),
      D.uniformizer = Subring.inclusion hOR π ∧ D.exponent = C.exponent ∧
      D.valuation = w ∧ StrictMono a ∧ a 0 = 0 ∧
      (∀ n, a (n + 1) = a n + l n + 1) ∧
      (∀ n, D.endpoint n = C.endpoint (a n)) ∧
      (∀ n, D.ratio n = sourceBlock t (a n) (l n)) ∧
      ∀ Λ : Set ℕ, D.AdmissibleTail Λ →
        D.NoOutsideJunkFactorization O Λ ∧
        ¬ Factorization.IsAtomicDomain (D.sourceSubring O Λ) ∧
        D.sourceSubring O Λ ≤ R ∧ O ≤ D.sourceSubring O Λ ∧
        ∀ x : D.sourceSubring O Λ, w (x : K) ≤ 1 := by
  let : Algebra (FractionRing O) K := (coefficientFractionEmbedding O).toAlgebra
  have halg (x : K) : IsAlgebraic (FractionRing O) x := by
    let : IsScalarTower O (FractionRing O) K :=
      IsScalarTower.of_algebraMap_eq fun z =>
        (coefficientFractionEmbedding_algebraMap O z).symm
    exact (Algebra.IsAlgebraic.isAlgebraic (R := O) x).extendScalars
      (IsFractionRing.injective O (FractionRing O))
  let I : BlockInput R (FractionRing O) K (Subring.inclusion hOR π) t := {
    chain := C
    embedding := R.subtype
    embedding_injective := Subtype.val_injective
    valuation := w
    coefficient_orders := fun z hz => coefficientFraction_order_integral O w hO hπ hnorm hz
    source_algebraic := fun r => halg (r : K)
    endpoint_order_ge_one := hc
    uniformizer_order := hnorm
    ratio_positive := ht }
  let v := coefficientFractionValuation O w
  have hπf0 : algebraMap O (FractionRing O) π ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective O (FractionRing O))).mpr hπ.ne_zero
  have hπford : realValuationOrder v (algebraMap O (FractionRing O) π) = 1 := by
    simpa only [v, coefficientFractionValuation, realValuationOrder,
      Valuation.comap_apply, coefficientFractionEmbedding_algebraMap] using hnorm
  have hπfv : v (algebraMap O (FractionRing O) π) < 1 :=
    (realValuationOrder_pos_iff v hπf0).mp (by rw [hπford]; norm_num)
  let := valuationNormCompletion_nontriviallyNormedField v hπf0 hπfv
  let := valuationCompletionNormedAlgebra v w (fun _ => rfl)
  let J := I.completed v (fun _ => rfl)
  have hJw (r : R) : J.valuation (J.embedding r) = w (r : K) :=
    completionValuation_algebraMap w (r : K)
  let D := J.toSourceBlockData BlockState.basisLoss w hJw
  have hsquare : (algebraMap (ValuationNormCompletion v) (ValuationNormCompletion w)).comp
      (algebraMap (FractionRing O) (ValuationNormCompletion v)) =
    (algebraMap K (ValuationNormCompletion w)).comp (coefficientFractionEmbedding O) := by
    ext z
    exact coefficientCompletionEmbedding_algebraMap O w z
  refine ⟨D, J.index BlockState.basisLoss, J.length BlockState.basisLoss,
    rfl, rfl, rfl, J.index_strictMono _, J.index_zero _, J.index_succ _,
    (fun _ => rfl), (fun _ => rfl), ?_⟩
  intro Λ hΛ
  have hk : ∀ n, 0 < n → ∀ p : Laurent (FractionRing O) n,
      p ∈ D.formalRing O π n → D.evaluation O n p = 0 →
        p ∈ modelKernelJunk (coefficientFractionValuation O w)
          (algebraMap O (FractionRing O) π) (D.modelParameters n) := by
    intro n _ p hp hz
    exact J.source_kernel_mem w hJw (fun _ => rfl) O π rfl hO
      (completionValuation v) (fun _ => rfl)
      (algebraMap (FractionRing O) (ValuationNormCompletion v))
      (completionValuation_algebraMap v)
      (algebraMap K (ValuationNormCompletion w)) (fun _ => rfl) hsquare p hp hz
  obtain ⟨hno, hna⟩ := D.source_certificate_of_kernel O π hπ rfl hO Λ hΛ hk
  exact ⟨hno, hna, D.sourceSubring_le O hOR Λ, D.coefficient_le_sourceSubring O Λ,
    D.sourceSubring_bounded O hO Λ⟩

/-- The local-chain obstruction for any prescribed nonzero local chain and any normalized real
valuation dominating the local source. The endpoint identity records the
actual uniformizer scaling `π * b * x (a n)`, and the blocks retain the original ratios.
No completion data, hereditary atomicity, or semilocal assumption remains. -/
theorem local_exists_source_certificate
    (O R : Subring K) [IsDiscreteValuationRing O] [IsLocalRing R]
    [IsFractionRing R K] [Algebra.IsAlgebraic O K] (hOR : O ≤ R)
    (π : O) (hπ : Irreducible π)
    (x t : ℕ → R) (hx : ∀ n, x n ≠ 0)
    (ht : ∀ n, t n ∈ IsLocalRing.maximalIdeal R)
    (hxt : ∀ n, x n = x (n + 1) * t n)
    (w : Valuation K ℝ≥0) (hnorm : realValuationOrder w (π : K) = 1)
    (hR : ∀ r : R, w (r : K) ≤ 1)
    (hcenter : ∀ r : R, r ≠ 0 →
      (0 < realValuationOrder w (r : K) ↔ r ∈ IsLocalRing.maximalIdeal R)) :
    ∃ (D : SourceBlockData R) (a l : ℕ → ℕ) (b : R),
      D.uniformizer = Subring.inclusion hOR π ∧ D.valuation = w ∧
      StrictMono a ∧ a 0 = 0 ∧ (∀ n, a (n + 1) = a n + l n + 1) ∧
      (∀ n, D.endpoint n = Subring.inclusion hOR π * b * x (a n)) ∧
      (∀ n, D.ratio n = sourceBlock t (a n) (l n)) ∧
      ∀ Λ : Set ℕ, D.AdmissibleTail Λ →
        D.NoOutsideJunkFactorization O Λ ∧
        ¬ Factorization.IsAtomicDomain (D.sourceSubring O Λ) ∧
        D.sourceSubring O Λ ≤ R ∧ O ≤ D.sourceSubring O Λ ∧
        (∀ z : D.sourceSubring O Λ, w (z : K) ≤ 1) ∧
        (∀ z : D.sourceSubring O Λ, (z : K) ∈ D.sourceJunk O → ¬ Irreducible z) ∧
        ¬ IsUnit (⟨D.endpoint 1, D.endpoint_mem_sourceSubring O Λ 1⟩ :
          D.sourceSubring O Λ) := by
  obtain ⟨C, b, hCb⟩ :=
    embedded_exists_uniformizerChainData_scaled O R hOR hπ x t hx ht hxt
  have hdiv : ∀ n, Subring.inclusion hOR π ∣ C.endpoint n := by
    intro n
    exact ⟨b * x n, by rw [hCb n]; ring⟩
  have hfloor := C.one_le_endpoint_order hdiv R.subtype Subtype.val_injective w hR hnorm
  have htpos : ∀ n, 0 < realValuationOrder w (t n : K) :=
    fun n => (hcenter (t n) (C.ratio_ne_zero n)).mpr (ht n)
  have hO : ∀ z : O, w (z : K) ≤ 1 := fun z => hR (Subring.inclusion hOR z)
  obtain ⟨D, a, l, hDπ, _, hDw, ha, ha0, hasucc, hDc, hDt, hcert⟩ :=
    UniformizerChainData.exists_completed_source_certificate O R hOR π hπ C w hO hnorm htpos hfloor
  refine ⟨D, a, l, b, hDπ, hDw, ha, ha0, hasucc,
    (fun n => (hDc n).trans (hCb (a n))), hDt, ?_⟩
  intro Λ hΛ
  obtain ⟨hno, hna, hle, hcoeff, hbound⟩ := hcert Λ hΛ
  have hOD : ∀ z : O, D.valuation (z : K) ≤ 1 := by simpa only [hDw] using hO
  refine ⟨hno, hna, hle, hcoeff, hbound, ?_, ?_⟩
  · intro z hz hirr
    exact D.sourceSubring_irreducible_not_mem_junk O hOD Λ hΛ.cofinal z hirr hz
  · apply not_isUnit_of_mapped_order_pos (D.sourceSubring O Λ).subtype w hbound
    change 0 < realValuationOrder w (D.endpoint 1 : K)
    rw [← hDw]
    exact zero_lt_one.trans_le (D.endpoint_order_ge_one 1)

/-- Normalize the real representative of a prescribed valuation ring over an
algebraic DVR base. Both the valuation ring and its maximal ideal are retained;
the construction does not replace the supplied place by a newly chosen place. -/
theorem exists_normalized_realValuation_of_valuationSubring
    (O : Subring K) [IsDiscreteValuationRing O] [Algebra.IsAlgebraic O K]
    (V : ValuationSubring K) (hOV : O ≤ V.toSubring)
    (π : O) (hπ : Irreducible π) (hπV : (π : K) ∈ V.nonunits) :
    ∃ w : Valuation K ℝ≥0, realValuationOrder w (π : K) = 1 ∧
      (∀ z : K, w z ≤ 1 ↔ z ∈ V) ∧
      ∀ z : K, z ≠ 0 → (0 < realValuationOrder w z ↔ z ∈ V.nonunits) := by
  classical
  have hπK : (π : K) ≠ 0 := Subtype.coe_ne_coe.mpr hπ.ne_zero
  have hπlt : V.valuation (π : K) < 1 := V.mem_nonunits_iff.mp hπV
  have hV : V ≠ ⊤ := by
    intro htop
    have hu : IsUnit (⟨(π : K), by simp⟩ : (⊤ : ValuationSubring K)) :=
      (isUnit_iff_ne_zero.mpr hπK).map
        (Subring.topEquiv : (⊤ : Subring K) ≃+* K).symm.toRingHom
    rw [htop] at hπlt
    exact hπlt.ne ((ValuationSubring.valuation_eq_one_iff ⊤ _).mp hu)
  let : IsFractionRing V.toSubring K := inferInstanceAs (IsFractionRing V K)
  let : Ring.KrullDimLE 1 V := embedded_dimensionLE_one_of_algebraic_dvr O V.toSubring hOV
  let : V.valuation.RankOne := Classical.choice (valuationSubring_nonempty_rankOne V hV)
  let v := ValuationApproximation.realValuation V.valuation
  have hequiv : v.IsEquiv V.valuation := ValuationApproximation.realValuation_isEquiv _
  have hcenter (z : K) : v z < 1 ↔ z ∈ V.nonunits := by
    simpa only [map_one] using
      (hequiv.lt_iff_lt (x := z) (y := (1 : K))).trans V.mem_nonunits_iff.symm
  have hpos : 0 < realValuationOrder v (π : K) :=
    (realValuationOrder_pos_iff v hπK).mpr ((hcenter _).mpr hπV)
  refine ⟨normalizeRealValuation v (π : K) hpos,
    realValuationOrder_normalize_self v (π : K) hpos, ?_, ?_⟩
  · intro z
    rw [normalizeRealValuation_le_one_iff]
    have he : v z ≤ 1 ↔ V.valuation z ≤ 1 := by
      simpa only [map_one] using hequiv z 1
    exact he.trans (V.valuation_le_one_iff z)
  · intro z hz
    exact (realValuationOrder_normalize_pos_iff v (π : K) hpos z).trans
      ((realValuationOrder_pos_iff v hz).trans (hcenter z))

/-- The local-chain obstruction at every prescribed valuation ring dominating the local source.
The certificate is built from blocks of the supplied chain, its endpoints are
literally `π * b * x (a n)`, and its source subring lies in `R ∩ V`. There are
no completed-field or valuation-normalization hypotheses. -/
theorem local_exists_source_certificate_at_valuationSubring
    (O R : Subring K) [IsDiscreteValuationRing O] [IsLocalRing R]
    [IsFractionRing R K] [Algebra.IsAlgebraic O K] (hOR : O ≤ R)
    (π : O) (hπ : Irreducible π)
    (x t : ℕ → R) (hx : ∀ n, x n ≠ 0)
    (ht : ∀ n, t n ∈ IsLocalRing.maximalIdeal R)
    (hxt : ∀ n, x n = x (n + 1) * t n)
    (V : ValuationSubring K) (hRV : R ≤ V.toSubring)
    (hcenter : ∀ r : R, (r : K) ∈ V.nonunits ↔ r ∈ IsLocalRing.maximalIdeal R) :
    ∃ (D : SourceBlockData R) (a l : ℕ → ℕ) (b : R),
      D.uniformizer = Subring.inclusion hOR π ∧
      (∀ z : K, D.valuation z ≤ 1 ↔ z ∈ V) ∧
      StrictMono a ∧ a 0 = 0 ∧ (∀ n, a (n + 1) = a n + l n + 1) ∧
      (∀ n, D.endpoint n = Subring.inclusion hOR π * b * x (a n)) ∧
      (∀ n, D.ratio n = sourceBlock t (a n) (l n)) ∧
      ∀ Λ : Set ℕ, D.AdmissibleTail Λ →
        D.NoOutsideJunkFactorization O Λ ∧
        ¬ Factorization.IsAtomicDomain (D.sourceSubring O Λ) ∧
        D.sourceSubring O Λ ≤ R ⊓ V.toSubring ∧ O ≤ D.sourceSubring O Λ ∧
        (∀ z : D.sourceSubring O Λ, (z : K) ∈ D.sourceJunk O → ¬ Irreducible z) ∧
        ¬ IsUnit (⟨D.endpoint 1, D.endpoint_mem_sourceSubring O Λ 1⟩ :
          D.sourceSubring O Λ) := by
  let : Algebra O R := (Subring.inclusion hOR).toAlgebra
  let : IsScalarTower O R K := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : Algebra.IsAlgebraic O R := Algebra.IsAlgebraic.tower_bot_of_injective
    (A := K) Subtype.val_injective
  have ht0 : t 0 ≠ 0 := by
    intro he
    exact hx 0 (by rw [hxt 0, he, mul_zero])
  have hfield : ¬ IsField R := by
    intro hf
    let : Field R := hf.toField
    exact (IsLocalRing.mem_maximalIdeal _).mp (ht 0) (isUnit_iff_ne_zero.mpr ht0)
  have hπR := uniformizer_mem_maximalIdeal (R := R) hπ hfield
  have hπV : (π : K) ∈ V.nonunits :=
    (hcenter (Subring.inclusion hOR π)).mpr hπR
  obtain ⟨w, hnorm, hval, hpos⟩ :=
    exists_normalized_realValuation_of_valuationSubring O V (hOR.trans hRV) π hπ hπV
  have hR : ∀ r : R, w (r : K) ≤ 1 := fun r => (hval r).mpr (hRV r.property)
  have hcw : ∀ r : R, r ≠ 0 →
      (0 < realValuationOrder w (r : K) ↔ r ∈ IsLocalRing.maximalIdeal R) := by
    intro r hr
    exact (hpos (r : K) (Subtype.coe_ne_coe.mpr hr)).trans (hcenter r)
  obtain ⟨D, a, l, b, hDπ, hDw, ha, ha0, hasucc, hDc, hDt, hcert⟩ :=
    local_exists_source_certificate O R hOR π hπ x t hx ht hxt w hnorm hR hcw
  refine ⟨D, a, l, b, hDπ, ?_, ha, ha0, hasucc, hDc, hDt, ?_⟩
  · simpa only [hDw] using hval
  · intro Λ hΛ
    obtain ⟨hno, hna, hle, hcoeff, hb, hatoms, hunit⟩ := hcert Λ hΛ
    refine ⟨hno, hna, le_inf hle ?_, hcoeff, hatoms, hunit⟩
    intro z hz
    exact (hval z).mp (hb ⟨z, hz⟩)

end HereditaryAtomicity.DVRBase
