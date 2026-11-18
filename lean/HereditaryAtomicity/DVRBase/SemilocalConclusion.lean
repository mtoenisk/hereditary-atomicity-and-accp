import HereditaryAtomicity.DVRBase.SemilocalReduction
import HereditaryAtomicity.DVRBase.SourceRings
import HereditaryAtomicity.DVRBase.SourceCertificateCore
import HereditaryAtomicity.DVRBase.SourceBlockAdapter
import HereditaryAtomicity.SemilocalACCP
import HereditaryAtomicity.FractionFieldImage

/-!
# The original-source intersection in the semilocal DVR-base argument

A local source obstruction is transferred to the literal intersection with the
original domain. Fresh quotients return through the other-stalk unit property;
no hereditary atomicity of a localization is used.
-/

noncomputable section
namespace HereditaryAtomicity.DVRBase
open scoped BigOperators NNReal
universe u
variable {K : Type u} [Field K]

/-- The semilocal intersection step. Positive-order fresh source divisors
and units at all other stalks make the local atomless ideal atomless in the
actual original-source intersection. The outside-ideal product obstruction
then contradicts hereditary atomicity of the original domain. -/
theorem not_hereditarilyAtomic_of_local_source_obstruction
    (D : Subring K) [IsFractionRing D K] (M : MaximalSpectrum D)
    (S : Subring K) (hS : S ≤ sourceMaximalStalk D M)
    (v : Valuation K ℝ≥0) (hv : ∀ s : S, v (s : K) ≤ 1)
    (J : Set K)
    (hJpos : ∀ g : K, g ∈ J → g ≠ 0 → 0 < realValuationOrder v g)
    (hfresh : ∀ g : K, g ∈ S → g ∈ J → g ≠ 0 →
      ∃ y : D, ∃ q : K, (y : K) ∈ S ∧ 0 < realValuationOrder v (y : K) ∧
        q ∈ S ∧ q ∈ J ∧ g = (y : K) * q ∧
        ∀ Q : MaximalSpectrum D, Q ≠ M → IsUnit (sourceMaximalMap D Q y))
    {z : K} (hz : z ≠ 0) (hzS : z ∈ S) (hzD : z ∈ D)
    (hno : ∀ (ι : Type u) [Fintype ι] (f : ι → K),
      (∀ i, f i ∈ S) → (∀ i, f i ∉ J) → (∏ i, f i) ≠ z) :
    ¬ Factorization.IsHereditarilyAtomic D := by
  have hbound : ∀ a : ↥(S ⊓ D), v (a : K) ≤ 1 :=
    fun a => hv ⟨a, a.property.1⟩
  have hunit : ∀ a : ↥(S ⊓ D), (a : K) ∈ J → ¬ IsUnit a := by
    intro a ha
    by_cases ha0 : a = 0
    · simpa only [ha0] using (not_isUnit_zero : ¬ IsUnit (0 : ↥(S ⊓ D)))
    · exact not_isUnit_of_mapped_order_pos (S ⊓ D).subtype v hbound
        (hJpos a ha (Subtype.coe_ne_coe.mpr ha0))
  have hsplit : ∀ a : ↥(S ⊓ D), (a : K) ∈ J →
      ∃ b c : ↥(S ⊓ D), ¬ IsUnit b ∧ ¬ IsUnit c ∧ a = b * c := by
    intro a ha
    by_cases ha0 : a = 0
    · exact ⟨0, 0, not_isUnit_zero, not_isUnit_zero, by simp [ha0]⟩
    have haK : (a : K) ≠ 0 := Subtype.coe_ne_coe.mpr ha0
    obtain ⟨y, q, hyS, hypos, hqS, hqJ, heq, hyunits⟩ :=
      hfresh a a.property.1 ha haK
    have hy0 : (y : K) ≠ 0 := by
      intro h
      exact haK (by simpa [h] using heq)
    have hq0 : q ≠ 0 := by
      intro h
      exact haK (by simpa [h] using heq)
    have hquot : (a : K) / (y : K) = q := by
      rw [heq, mul_div_cancel_left₀ _ hy0]
    have hqD : q ∈ D := by
      rw [← hquot]
      exact source_div_mem_of_stalk_and_units D M a.property.2 y
        (hquot ▸ hS hqS) hyunits
    let b : ↥(S ⊓ D) := ⟨y, hyS, y.property⟩
    let c : ↥(S ⊓ D) := ⟨q, hqS, hqD⟩
    refine ⟨b, c, ?_, ?_, Subtype.ext heq⟩
    · exact not_isUnit_of_mapped_order_pos (S ⊓ D).subtype v hbound hypos
    · exact not_isUnit_of_mapped_order_pos (S ⊓ D).subtype v hbound (hJpos q hqJ hq0)
  have hnot : ¬ Factorization.IsAtomicDomain ↥(S ⊓ D) := by
    apply not_isAtomicDomain_intersection S D J hz hzS hzD hunit hsplit
    intro ι _ f hprod hout
    apply hno ι (fun i => (f i : K)) (fun i => (f i).property) hout
    simpa only [SubmonoidClass.coe_finsetProd] using
      congrArg (fun a : S => (a : K)) hprod
  intro hD
  exact hnot (hD.of_injective (Subring.inclusion inf_le_right)
    (Subring.inclusion_injective inf_le_right)).isAtomicDomain


/-- The semilocal intersection for the literal rings and ideal of a selected source block chain.
Only the endpoint and selected ratios return to the original domain;
first-dead power-return witnesses stay in the chosen stalk. -/
theorem SourceBlockData.not_hereditarilyAtomic_of_no_factorization
    (D : Subring K) [IsFractionRing D K] (M : MaximalSpectrum D)
    (B : SourceBlockData (sourceMaximalStalk D M))
    (O : Subring K) (hOlocal : O ≤ sourceMaximalStalk D M)
    (hO : ∀ a : O, B.valuation (a : K) ≤ 1)
    (Λ : Set ℕ) (hcofinal : ∀ N : ℕ, ∃ m, N ≤ m ∧ m ∈ Λ)
    (sourceRatio : ℕ → D) (hratio : ∀ m, (sourceRatio m : K) = (B.ratio m : K))
    (hunits : ∀ m (Q : MaximalSpectrum D), Q ≠ M →
      IsUnit (sourceMaximalMap D Q (sourceRatio m)))
    (hzD : (B.endpoint 1 : K) ∈ D)
    (hno : B.NoOutsideJunkFactorization O Λ) :
    ¬ Factorization.IsHereditarilyAtomic D := by
  refine not_hereditarilyAtomic_of_local_source_obstruction D M
    (B.sourceSubring O Λ) (B.sourceSubring_le O hOlocal Λ) B.valuation
    (B.sourceSubring_bounded O hO Λ) (B.sourceJunk O)
    (fun _ hg hg0 => B.sourceJunk_order_pos O hO hg hg0) ?_
    (Subtype.coe_ne_coe.mpr (B.endpoint_ne_zero 1))
    (B.endpoint_mem_sourceSubring O Λ 1) hzD ?_
  · intro g _ hg hg0
    obtain ⟨m, _, _, q, hq, heq, hy, hypos, _⟩ :=
      B.sourceJunk_fresh_split O hO Λ hcofinal hg hg0 0
    refine ⟨sourceRatio m, q, ?_, ?_, B.sourceJunk_le_sourceSubring O Λ hq,
      hq, ?_, hunits m⟩
    · rwa [hratio m]
    · rwa [hratio m]
    · rwa [hratio m]
  · intro ι _ f hf hout heq
    let e := Fintype.equivFin ι
    apply hno (Fintype.card ι) (fun i => f (e.symm i))
      (fun i => hf (e.symm i)) (fun i => hout (e.symm i))
    exact (e.symm.prod_comp f).trans heq


/-- A field and each of its actual maximal localizations satisfy ACCP. -/
theorem maximal_stalk_wfDvdMonoid_of_isField
    {R : Type*} [CommRing R] [IsDomain R] (hfield : IsField R)
    (M : MaximalSpectrum R) : WfDvdMonoid (Localization.AtPrime M.asIdeal) := by
  let : Field R := hfield.toField
  let e : R ≃+* Localization.AtPrime M.asIdeal := RingEquiv.ofBijective
    (algebraMap R (Localization.AtPrime M.asIdeal))
    (hfield.localization_map_bijective (M := M.asIdeal.primeCompl)
      (by exact fun h => h M.asIdeal.zero_mem))
  exact (Factorization.wfDvdMonoid_ringEquiv_iff e).mpr inferInstance

/-- A ring equivalence transports ACCP at every actual maximal stalk. This
retains the maximal ideal correspondence when passing to the fraction image. -/
theorem maximal_stalks_wfDvdMonoid_of_ringEquiv
    {R A : Type*} [CommRing R] [CommRing A] (e : R ≃+* A)
    (hA : ∀ Q : MaximalSpectrum A, WfDvdMonoid (Localization.AtPrime Q.asIdeal))
    (M : MaximalSpectrum R) : WfDvdMonoid (Localization.AtPrime M.asIdeal) := by
  let Q : MaximalSpectrum A :=
    ⟨M.asIdeal.comap e.symm.toRingHom, Ideal.comap_isMaximal_of_equiv e.symm⟩
  have hMQ : M.asIdeal = Q.asIdeal.comap e.toRingHom := by
    dsimp [Q]
    rw [Ideal.comap_comap, RingEquiv.symm_comp, Ideal.comap_id]
  exact Factorization.wfDvdMonoid_of_ringEquiv
    (Localization.localRingEquiv M.asIdeal Q.asIdeal e hMQ) (hA Q)

/-- Transport an embedded-source stalk theorem to arbitrary semilocal domains.
This is a representation adapter; its explicit input is the embedded theorem. -/
theorem maximal_stalks_of_embedded_source_result
    (hembedded : ∀ (L : Type u) [Field L] (D : Subring L)
      [IsFractionRing D L] [Finite (MaximalSpectrum D)],
      Factorization.IsHereditarilyAtomic D → ¬ IsField D →
        ∀ M : MaximalSpectrum D, WfDvdMonoid (Localization.AtPrime M.asIdeal))
    {R : Type u} [CommRing R] [IsDomain R] [Finite (MaximalSpectrum R)]
    (hR : Factorization.IsHereditarilyAtomic R) (M : MaximalSpectrum R) :
    WfDvdMonoid (Localization.AtPrime M.asIdeal) := by
  classical
  by_cases hfield : IsField R
  · exact maximal_stalk_wfDvdMonoid_of_isField hfield M
  let L := FractionRing R
  let D := (algebraMap R L).range
  let : IsFractionRing D L := isFractionRing_fractionImage R L
  let : Finite (MaximalSpectrum D) := finite_maximalSpectrum_fractionImage R L
  let e : R ≃+* D := fractionImageEquiv R L
  have hD : Factorization.IsHereditarilyAtomic D := hereditarilyAtomic_fractionImage R L hR
  have hDf : ¬ IsField D := fun h => hfield (e.toMulEquiv.isField_congr.mpr h)
  exact maximal_stalks_wfDvdMonoid_of_ringEquiv e (hembedded L D hD hDf) M


/-- The local-to-global ACCP conclusion after the embedded stalk theorem has
been proved. This adapter includes fields and arbitrary source representations. -/
theorem wfDvdMonoid_of_embedded_source_result
    (hembedded : ∀ (L : Type u) [Field L] (D : Subring L)
      [IsFractionRing D L] [Finite (MaximalSpectrum D)],
      Factorization.IsHereditarilyAtomic D → ¬ IsField D →
        ∀ M : MaximalSpectrum D, WfDvdMonoid (Localization.AtPrime M.asIdeal))
    {R : Type u} [CommRing R] [IsDomain R] [Finite (MaximalSpectrum R)]
    (hR : Factorization.IsHereditarilyAtomic R) : WfDvdMonoid R :=
  wfDvdMonoid_of_maximal_localizations (maximal_stalks_of_embedded_source_result hembedded hR)

/-- Hereditary ACCP follows from the proved embedded stalk theorem and the
existing semilocal hereditary transfer; no HA localization premise is used. -/
theorem hereditarilyACCP_of_embedded_source_result
    (hembedded : ∀ (L : Type u) [Field L] (D : Subring L)
      [IsFractionRing D L] [Finite (MaximalSpectrum D)],
      Factorization.IsHereditarilyAtomic D → ¬ IsField D →
        ∀ M : MaximalSpectrum D, WfDvdMonoid (Localization.AtPrime M.asIdeal))
    {R : Type u} [CommRing R] [IsDomain R] [Finite (MaximalSpectrum R)]
    (hR : Factorization.IsHereditarilyAtomic R) : Factorization.IsHereditarilyACCP R :=
  hereditarilyACCP_of_maximal_localizations hR
    (maximal_stalks_of_embedded_source_result hembedded hR)


namespace SemilocalChainSetup
variable {D : Subring K} [IsFractionRing D K] {M : MaximalSpectrum D}
    (H : SemilocalChainSetup D M)
    {k L : Type*} [Field k] [Field L] [Algebra k L]
    (I : BlockInput (sourceMaximalStalk D M) k L
      (Subring.inclusion H.base_le H.uniformizer)
      (fun n => sourceMaximalMap D M (H.ratio n)))
    (loss : ℕ → BlockState k L → ℝ)

/-- The actual original-source representative of each recursively selected
block. BlockInput.length counts the entries after the first, hence the +1. -/
def selectedSourceRatio (n : ℕ) : D :=
  ∏ i ∈ Finset.range (I.length loss n + 1), H.ratio (I.index loss n + i)

@[simp] theorem selectedSourceRatio_coe (n : ℕ) :
    (H.selectedSourceRatio I loss n : K) = (I.sourceY loss n : K) := by
  simp only [selectedSourceRatio, BlockInput.sourceY, sourceBlock,
    SubmonoidClass.coe_finsetProd, coe_sourceMaximalMap]

theorem selectedSourceRatio_unit_elsewhere (n : ℕ) (Q : MaximalSpectrum D) (hQM : Q ≠ M) :
    IsUnit (sourceMaximalMap D Q (H.selectedSourceRatio I loss n)) :=
  H.ratio_block_isUnit_elsewhere (I.index loss n) (I.length loss n + 1) Q hQM

/-- Recursive block endpoints remain original-source endpoints of the same
prescribed local chain, not newly chosen elements of equal valuation. -/
theorem selectedEndpoint_mem_source (hchain : I.chain = H.chain) (n : ℕ) :
    (I.sourceZ loss n : K) ∈ D := by
  change (I.chain.endpoint (I.index loss n) : K) ∈ D
  rw [hchain]
  exact H.endpoint_source (I.index loss n)

/-- The original-source semilocal contradiction for an actual recursive
block input. The source transfer theorem supplies the stated factorization obstruction. -/
theorem not_hereditarilyAtomic_of_selected_certificate
    (hchain : I.chain = H.chain)
    (hw : ∀ r : sourceMaximalStalk D M, I.valuation (I.embedding r) = H.valuation (r : K))
    (Λ : Set ℕ) (hcofinal : ∀ N : ℕ, ∃ m, N ≤ m ∧ m ∈ Λ)
    (hno : (I.toSourceBlockData loss H.valuation hw).NoOutsideJunkFactorization H.base Λ) :
    ¬ Factorization.IsHereditarilyAtomic D := by
  apply SourceBlockData.not_hereditarilyAtomic_of_no_factorization D M
    (I.toSourceBlockData loss H.valuation hw) H.base H.base_le
    (fun a => H.bounded (Subring.inclusion H.base_le a)) Λ hcofinal
    (H.selectedSourceRatio I loss) (fun m => H.selectedSourceRatio_coe I loss m)
    (fun m Q hQM => H.selectedSourceRatio_unit_elsewhere I loss m Q hQM)
    (H.selectedEndpoint_mem_source I loss hchain 1) hno

end SemilocalChainSetup

end HereditaryAtomicity.DVRBase
