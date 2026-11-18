import HereditaryAtomicity.DVRBase.CommonSupportCertificate
import HereditaryAtomicity.DVRBase.CoefficientDivision
import HereditaryAtomicity.DVRBase.ArithmeticCoefficientBase

/-!
# Concrete common-support chain clients

The inside-base client derives power scaling and uniform radical returns over
all selected stalks, even for an infinite support. The output retains actual
blocks of the original chain and the literal nonatomic source intersection.
-/

noncomputable section
namespace HereditaryAtomicity.DVRBase
open scoped NNReal
variable {K : Type*} [Field K]

/-- The original top divides a uniformizer power inside the actual common
support ring. No locality or finiteness of the support is needed. -/
theorem common_support_exists_power_scaling
    (D O : Subring K) [IsFractionRing D K] [IsDiscreteValuationRing O]
    [Algebra.IsAlgebraic O K] (places : Set (MaximalSpectrum D))
    (hOA : ∀ Q ∈ places, O ≤ sourceMaximalStalk D Q)
    (π : O) (hπ : Irreducible π) (x : D) (hx : x ≠ 0) :
    ∃ (k : ℕ) (b : commonSupportRing D places),
      (π : K) ^ k = (x : K) * (b : K) := by
  let A := commonSupportRing D places
  have hOA' : O ≤ A := le_iInf fun Q => hOA Q.val Q.property
  let : Algebra O A := (Subring.inclusion hOA').toAlgebra
  let : IsScalarTower O A K := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : Algebra.IsAlgebraic O A := Algebra.IsAlgebraic.tower_bot_of_injective
    (A := K) Subtype.val_injective
  let xA : A := Subring.inclusion (source_le_commonSupportRing D places) x
  have hxA : xA ≠ 0 := fun hz => hx (Subtype.ext (congrArg A.subtype hz))
  obtain ⟨k, b, hb⟩ := exists_dvd_uniformizer_pow hπ hxA
  exact ⟨k, b, congrArg A.subtype hb⟩

/-- Every original ratio has a single positive power returning through all
selected stalks. The exponent may depend on the ratio but not on the place. -/
theorem common_support_ratio_radical_returns
    (D O : Subring K) [IsFractionRing D K] [IsDiscreteValuationRing O]
    [Algebra.IsAlgebraic O K] (places : Set (MaximalSpectrum D))
    (hOA : ∀ Q ∈ places, O ≤ sourceMaximalStalk D Q)
    (π : O) (hπ : Irreducible π) (t : ℕ → D)
    (ht : ∀ n Q, Q ∈ places → t n ∈ Q.asIdeal) :
    ∀ n, ∃ e : ℕ, 0 < e ∧
      (t n : K) ^ e / (π : K) ∈ commonSupportRing D places := by
  intro n
  obtain ⟨e, he, hret⟩ :=
    exists_pos_pow_div_mem_at_nonunit_stalks D O places hOA π hπ 1 (t n)
  refine ⟨e, he, Subring.mem_iInf.mpr fun Q => ?_⟩
  simpa only [pow_one] using hret Q.val Q.property (ht n Q.val Q.property)

/-- A normalized valuation at a chosen common-support center. It is bounded
on the actual common-support ring and positive on every original ratio. -/
theorem common_support_exists_normalized_valuation
    (D O : Subring K) [IsFractionRing D K] [IsDiscreteValuationRing O]
    [Algebra.IsAlgebraic O K] (places : Set (MaximalSpectrum D))
    (hOA : ∀ Q ∈ places, O ≤ sourceMaximalStalk D Q)
    (M : MaximalSpectrum D) (hM : M ∈ places)
    (π : O) (hπ : Irreducible π) (hπD : (π : K) ∈ D)
    (hπM : (⟨π, hπD⟩ : D) ∈ M.asIdeal)
    (t : ℕ → D) (ht0 : ∀ n, t n ≠ 0) (htM : ∀ n, t n ∈ M.asIdeal) :
    ∃ w : Valuation K ℝ≥0, realValuationOrder w (π : K) = 1 ∧
      (∀ z : O, w (z : K) ≤ 1) ∧
      (∀ z : commonSupportRing D places, w (z : K) ≤ 1) ∧
      ∀ n, 0 < realValuationOrder w (t n : K) := by
  let R := sourceMaximalStalk D M
  let S := Localization.subalgebra.ofField K M.asIdeal.primeCompl
    M.asIdeal.primeCompl_le_nonZeroDivisors
  let : Algebra D R := inferInstanceAs (Algebra D S)
  let : IsLocalization.AtPrime R M.asIdeal := inferInstanceAs (IsLocalization.AtPrime S M.asIdeal)
  let : IsLocalRing R := IsLocalization.AtPrime.isLocalRing R M.asIdeal
  let : IsFractionRing R K := isFractionRing_of_subring_le D R (le_sourceMaximalStalk D M)
  let πR : R := Subring.inclusion (hOA M hM) π
  have hpR : πR ∈ IsLocalRing.maximalIdeal R := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    exact (isUnit_sourceMaximalMap_iff D M ⟨π, hπD⟩).mp hu hπM
  obtain ⟨w, hnorm, hR, hcenter⟩ :=
    exists_normalized_dominating_realValuation_of_algebraic_dvr O R (hOA M hM)
      πR (fun hz => hπ.ne_zero (Subtype.ext (congrArg R.subtype hz))) hpR
  refine ⟨w, hnorm, fun z => hR (Subring.inclusion (hOA M hM) z),
    fun z => hR ⟨z, commonSupportRing_le_stalk D places M hM z.property⟩, ?_⟩
  intro n
  apply (hcenter (sourceMaximalMap D M (t n))
    (fun hz => ht0 n (Subtype.ext (congrArg R.subtype hz)))).mpr
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  exact fun hu => (isUnit_sourceMaximalMap_iff D M (t n)).mp hu (htM n)

/-- Over an algebraic DVR contained in the common support, consecutive blocks and their
source intersection give an element without an irreducible factorization. -/
theorem common_support_exists_source_certificate
    (D O : Subring K) [IsFractionRing D K] [IsDiscreteValuationRing O]
    [Algebra.IsAlgebraic O K] (places : Set (MaximalSpectrum D))
    (hplaces : places.Nonempty) (hOA : ∀ Q ∈ places, O ≤ sourceMaximalStalk D Q)
    (π : O) (hπ : Irreducible π) (hπD : (π : K) ∈ D)
    (hπsupport : ∀ Q ∈ places, (⟨π, hπD⟩ : D) ∈ Q.asIdeal)
    (x t : ℕ → D) (hx : ∀ n, x n ≠ 0)
    (hxt : ∀ n, x n = x (n + 1) * t n)
    (hsupport : ∀ n (Q : MaximalSpectrum D), t n ∈ Q.asIdeal ↔ Q ∈ places) :
    ∃ (k : ℕ) (b : commonSupportRing D places) (w : Valuation K ℝ≥0),
      realValuationOrder w (π : K) = 1 ∧
      (π : K) ^ k = (x 0 : K) * (b : K) ∧
      ∃ (F : SourceBlockData (commonSupportRing D places)) (a l : ℕ → ℕ),
        (F.uniformizer : K) = (π : K) ∧ F.exponent = k + 1 ∧ F.valuation = w ∧
        StrictMono a ∧ a 0 = 0 ∧ (∀ n, a (n + 1) = a n + l n + 1) ∧
        (∀ n, (F.endpoint n : K) = (π : K) * (b : K) * (x (a n) : K)) ∧
        (∀ n, (F.endpoint n : K) ∈ D) ∧
        (∀ n, (F.ratio n : K) = ((sourceBlock t (a n) (l n) : D) : K)) ∧
        ∀ Λ : Set ℕ, F.AdmissibleTail Λ →
          F.NoOutsideJunkFactorization O Λ ∧
          F.sourceSubring O Λ ≤ commonSupportRing D places ∧
          F.IntersectionCertificate D O Λ := by
  obtain ⟨M, hM⟩ := hplaces
  obtain ⟨k, b, hb⟩ := common_support_exists_power_scaling D O places hOA π hπ (x 0) (hx 0)
  have ht0 (n : ℕ) : t n ≠ 0 := by
    intro hz
    exact hx n (by rw [hxt n, hz, mul_zero])
  obtain ⟨w, hnorm, hO, hA, htpos⟩ := common_support_exists_normalized_valuation
    D O places hOA M hM π hπ hπD (hπsupport M hM) t ht0
    (fun n => (hsupport n M).mpr hM)
  have hAF := uniformizerDivisionClosed_of_dvr O π hπ w hO hnorm
  have hOA' : O ≤ commonSupportRing D places := le_iInf fun Q => hOA Q.val Q.property
  refine ⟨k, b, w, hnorm, hb, ?_⟩
  exact common_support_exists_shrunk_certificate_of_scaling D O O places le_rfl hOA' π
    (by change Irreducible π; exact hπ) x t hx hxt (fun n Q => (hsupport n Q).mp) k b hb
    (D.pow_mem hπD _) (common_support_ratio_radical_returns D O places hOA π hπ t
      (fun n Q => (hsupport n Q).mpr)) w hO hA hnorm hAF htpos

/-- The common-support source intersection contradicts HA of the original
source, without applying HA to any stalk or overring. -/
theorem common_support_not_hereditarilyAtomic
    (D O : Subring K) [IsFractionRing D K] [IsDiscreteValuationRing O]
    [Algebra.IsAlgebraic O K] (places : Set (MaximalSpectrum D))
    (hplaces : places.Nonempty) (hOA : ∀ Q ∈ places, O ≤ sourceMaximalStalk D Q)
    (π : O) (hπ : Irreducible π) (hπD : (π : K) ∈ D)
    (hπsupport : ∀ Q ∈ places, (⟨π, hπD⟩ : D) ∈ Q.asIdeal)
    (x t : ℕ → D) (hx : ∀ n, x n ≠ 0)
    (hxt : ∀ n, x n = x (n + 1) * t n)
    (hsupport : ∀ n (Q : MaximalSpectrum D), t n ∈ Q.asIdeal ↔ Q ∈ places) :
    ¬ Factorization.IsHereditarilyAtomic D := by
  obtain ⟨k, b, w, _, _, F, a, l, _, _, _, _, _, _, _, _, _, hcert⟩ :=
    common_support_exists_source_certificate D O places hplaces hOA π hπ hπD hπsupport
      x t hx hxt hsupport
  obtain ⟨N, _, hN⟩ := F.exists_admissibleTail
  have hnot := (hcert (Set.Ici N) hN).2.2.not_atomic
  intro hD
  exact hnot (hD.of_injective (Subring.inclusion inf_le_right)
    (Subring.inclusion_injective inf_le_right)).isAtomicDomain

/-- A DVR over the prime field can lie both in the outside model DVR and in every selected
stalk. With the stated hypothesis on the source intersections, the construction gives
the normalized blocks and their intersection certificate for possibly infinite
support. -/
theorem outside_common_support_exists_source_certificate
    (p : ℕ) [Fact p.Prime] [CharP K p]
    (D O : Subring K) [IsFractionRing D K] [IsDiscreteValuationRing O]
    [Algebra.IsAlgebraic O K] (places : Set (MaximalSpectrum D))
    (M : MaximalSpectrum D) (hM : M ∈ places)
    (π : O) (hπ : Irreducible π) (hπD : (π : K) ∈ D)
    (hπsupport : ∀ Q ∈ places, (⟨π, hπD⟩ : D) ∈ Q.asIdeal)
    (V : ValuationSubring K) (hOV : O ≤ V.toSubring)
    (hMV : sourceMaximalStalk D M ≤ V.toSubring)
    (hcenter : ∀ d : D, d ∈ M.asIdeal → (d : K) ∈ V.nonunits)
    (x t : ℕ → D) (hx : ∀ n, x n ≠ 0)
    (hxt : ∀ n, x n = x (n + 1) * t n)
    (hsupport : ∀ n (Q : MaximalSpectrum D), t n ∈ Q.asIdeal ↔ Q ∈ places)
    (k : ℕ) (hk : 0 < k) (b : commonSupportRing D places)
    (hb : (π : K) ^ k = (x 0 : K) * (b : K))
    (hr : ∀ n, ∃ e : ℕ, 0 < e ∧
      (t n : K) ^ e / (π : K) ∈ commonSupportRing D places) :
    letI := ZMod.algebra K p
    ∃ (htr : Transcendental (ZMod p) (π : K)) (B : Subring K),
      B = arithmeticCoefficientRing (π : K) htr ∧ B ≤ O ∧
      B ≤ commonSupportRing D places ∧
      ∃ (w : Valuation K ℝ≥0) (F : SourceBlockData (commonSupportRing D places))
        (a l : ℕ → ℕ),
        realValuationOrder w (π : K) = 1 ∧
        (F.uniformizer : K) = (π : K) ∧ F.exponent = k + 1 ∧ 2 ≤ F.exponent ∧
        F.valuation = w ∧ StrictMono a ∧ a 0 = 0 ∧
        (∀ n, a (n + 1) = a n + l n + 1) ∧
        (∀ n, (F.endpoint n : K) = (π : K) * (b : K) * (x (a n) : K)) ∧
        (∀ n, (F.endpoint n : K) ∈ D) ∧
        (∀ n, (F.ratio n : K) = ((sourceBlock t (a n) (l n) : D) : K)) ∧
        ∀ Λ : Set ℕ, F.AdmissibleTail Λ →
          F.NoOutsideJunkFactorization B Λ ∧
          F.sourceSubring B Λ ≤ commonSupportRing D places ∧
          F.IntersectionCertificate D B Λ := by
  let : Algebra (ZMod p) K := ZMod.algebra K p
  let πD : D := ⟨π, hπD⟩
  obtain ⟨w, hnorm, hval, hpos⟩ :=
    exists_normalized_realValuation_of_valuationSubring O V hOV π hπ
      (hcenter πD (hπsupport M hM))
  have hO : ∀ z : O, w (z : K) ≤ 1 := fun z => (hval _).mpr (hOV z.property)
  have hA : ∀ z : commonSupportRing D places, w (z : K) ≤ 1 :=
    fun z => (hval _).mpr (hMV (commonSupportRing_le_stalk D places M hM z.property))
  have htpos (n : ℕ) : 0 < realValuationOrder w (t n : K) := by
    have ht0 : (t n : K) ≠ 0 := by
      intro hz
      have htz : t n = 0 := Subtype.ext hz
      exact hx n (by rw [hxt n, htz, mul_zero])
    exact (hpos _ ht0).mpr (hcenter (t n) ((hsupport n M).mpr hM))
  obtain ⟨htr, B, πB, hBO, hB, _, hπB, _, hπBO, hAF, _, hstalk⟩ :=
    exists_primeField_coefficient_base p D O πD π rfl hπ w hO hnorm
  have hBA : B ≤ commonSupportRing D places := by
    apply le_iInf
    intro Q
    simpa only [ofPrime_eq_localization_ofField, sourceMaximalStalk] using
      hstalk Q.val (hπsupport Q.val Q.property)
  obtain ⟨F, a, l, hFπ, hFexp, hFw, ha, ha0, hasucc, hFc, hFD, hFt, hcert⟩ :=
    common_support_exists_shrunk_certificate_of_scaling D B O places hBO hBA πB hπBO
      x t hx hxt (fun n Q => (hsupport n Q).mp) k b (by simpa only [hπB] using hb)
      (by simpa only [hπB] using D.pow_mem hπD (k + 1))
      (by simpa only [hπB] using hr) w hO hA (by simpa only [hπB] using hnorm) hAF htpos
  refine ⟨htr, B, hB, hBO, hBA, w, F, a, l, hnorm, hFπ.trans hπB,
    hFexp, ?_, hFw, ha, ha0, hasucc, ?_, hFD, hFt, hcert⟩
  · omega
  · simpa only [hπB] using hFc

/-- The exact outside-base common-support construction rules out HA of the
original characteristic-p source. It does not invoke HA of any overring. -/
theorem outside_common_support_not_hereditarilyAtomic
    (p : ℕ) [Fact p.Prime] [CharP K p]
    (D O : Subring K) [IsFractionRing D K] [IsDiscreteValuationRing O]
    [Algebra.IsAlgebraic O K] (places : Set (MaximalSpectrum D))
    (M : MaximalSpectrum D) (hM : M ∈ places)
    (π : O) (hπ : Irreducible π) (hπD : (π : K) ∈ D)
    (hπsupport : ∀ Q ∈ places, (⟨π, hπD⟩ : D) ∈ Q.asIdeal)
    (V : ValuationSubring K) (hOV : O ≤ V.toSubring)
    (hMV : sourceMaximalStalk D M ≤ V.toSubring)
    (hcenter : ∀ d : D, d ∈ M.asIdeal → (d : K) ∈ V.nonunits)
    (x t : ℕ → D) (hx : ∀ n, x n ≠ 0)
    (hxt : ∀ n, x n = x (n + 1) * t n)
    (hsupport : ∀ n (Q : MaximalSpectrum D), t n ∈ Q.asIdeal ↔ Q ∈ places)
    (k : ℕ) (hk : 0 < k) (b : commonSupportRing D places)
    (hb : (π : K) ^ k = (x 0 : K) * (b : K))
    (hr : ∀ n, ∃ e : ℕ, 0 < e ∧
      (t n : K) ^ e / (π : K) ∈ commonSupportRing D places) :
    ¬ Factorization.IsHereditarilyAtomic D := by
  obtain ⟨htr, B, _, _, _, w, F, a, l, _, _, _, _, _, _, _, _, _, _, _, hcert⟩ :=
    outside_common_support_exists_source_certificate p D O places M hM π hπ hπD hπsupport
      V hOV hMV hcenter x t hx hxt hsupport k hk b hb hr
  obtain ⟨N, _, hN⟩ := F.exists_admissibleTail
  have hnot := (hcert (Set.Ici N) hN).2.2.not_atomic
  intro hD
  exact hnot (hD.of_injective (Subring.inclusion inf_le_right)
    (Subring.inclusion_injective inf_le_right)).isAtomicDomain

end HereditaryAtomicity.DVRBase
