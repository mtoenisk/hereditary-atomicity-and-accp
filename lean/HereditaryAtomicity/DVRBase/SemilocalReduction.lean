import HereditaryAtomicity.DVRBase.SourceBase
import HereditaryAtomicity.DVRBase.ValuationReduction
import HereditaryAtomicity.DVRBase.SourceIntersection
import HereditaryAtomicity.CharP.SourceChain

/-!
# Original-source data for the semilocal DVR-base reduction

The valuation and power-return witnesses belong to the chosen maximal stalk.
The ratios and scaled endpoints are retained as actual elements of the original
source. No hereditary atomicity of a localization is assumed.
-/

noncomputable section
namespace HereditaryAtomicity.DVRBase
open scoped BigOperators NNReal

variable {K : Type*} [Field K]

/-- The actual maximal localization of an embedded source, inside its fraction field. -/
abbrev sourceMaximalStalk (D : Subring K) [IsFractionRing D K]
    (M : MaximalSpectrum D) : Subring K :=
  (Localization.subalgebra.ofField K M.asIdeal.primeCompl
    M.asIdeal.primeCompl_le_nonZeroDivisors).toSubring

theorem le_sourceMaximalStalk (D : Subring K) [IsFractionRing D K]
    (M : MaximalSpectrum D) : D ≤ sourceMaximalStalk D M := by
  intro x hx
  exact (Localization.subalgebra.ofField K M.asIdeal.primeCompl
    M.asIdeal.primeCompl_le_nonZeroDivisors).algebraMap_mem (⟨x, hx⟩ : D)

/-- The original-source map into its actual maximal stalk. -/
def sourceMaximalMap (D : Subring K) [IsFractionRing D K] (M : MaximalSpectrum D) :
    D →+* sourceMaximalStalk D M := Subring.inclusion (le_sourceMaximalStalk D M)

@[simp] theorem coe_sourceMaximalMap (D : Subring K) [IsFractionRing D K]
    (M : MaximalSpectrum D) (d : D) : (sourceMaximalMap D M d : K) = (d : K) := rfl

/-- Maximal-stalk membership is an exact test for original-source membership. -/
theorem mem_source_iff_mem_stalks (D : Subring K) [IsFractionRing D K] (z : K) :
    z ∈ D ↔ ∀ M : MaximalSpectrum D, z ∈ sourceMaximalStalk D M :=
  mem_iff_mem_maximal_localizations D z

/-- Source avoidance of a maximal ideal is exactly unit status at that stalk. -/
theorem isUnit_sourceMaximalMap_iff (D : Subring K) [IsFractionRing D K]
    (M : MaximalSpectrum D) (d : D) :
    IsUnit (sourceMaximalMap D M d) ↔ d ∉ M.asIdeal := by
  let S := Localization.subalgebra.ofField K M.asIdeal.primeCompl
    M.asIdeal.primeCompl_le_nonZeroDivisors
  let : Algebra D (sourceMaximalStalk D M) := inferInstanceAs (Algebra D S)
  let : IsLocalization.AtPrime (sourceMaximalStalk D M) M.asIdeal :=
    inferInstanceAs (IsLocalization.AtPrime S M.asIdeal)
  exact IsLocalization.AtPrime.isUnit_to_map_iff (sourceMaximalStalk D M) M.asIdeal d

/-- Division returns to the original source when the chosen-stalk quotient
exists and the source denominator is a unit at every other maximal stalk. -/
theorem source_div_mem_of_stalk_and_units (D : Subring K) [IsFractionRing D K]
    (M : MaximalSpectrum D) {g : K} (hg : g ∈ D) (y : D)
    (hchosen : g / (y : K) ∈ sourceMaximalStalk D M)
    (hunits : ∀ Q : MaximalSpectrum D, Q ≠ M → IsUnit (sourceMaximalMap D Q y)) :
    g / (y : K) ∈ D := by
  apply div_mem_of_mem_at_chosen_and_units_elsewhere D (sourceMaximalStalk D)
    (mem_source_iff_mem_stalks D) M hg y.property hchosen
  exact hunits

/-- The scaled endpoint is literally its uniformizer-power top divided by
the preceding ratios; this identity uses the prescribed source chain. -/
theorem UniformizerChainData.map_endpoint_eq_div_prod
    {R : Type*} [CommRing R] {π : R} {t : ℕ → R}
    (C : UniformizerChainData π t) (f : R →+* K) (hf : Function.Injective f) (n : ℕ) :
    f (C.endpoint n) = f π ^ C.exponent / ∏ i ∈ Finset.range n, f (t i) := by
  have hp : (∏ i ∈ Finset.range n, f (t i)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun i _ => (map_ne_zero_iff f hf).mpr (C.ratio_ne_zero i))
  apply (eq_div_iff hp).mpr
  have h := congrArg f (sourceChain_prefix_product C.endpoint t C.step n)
  rw [C.top, map_pow, map_mul, map_prod] at h
  exact h.symm

/-- The local scaling retains actual original-source endpoints. Only the
ratios, not the uniformizer, need to be units at the other stalks. -/
theorem UniformizerChainData.endpoints_mem_source
    (D : Subring K) [IsFractionRing D K] (M : MaximalSpectrum D)
    (π : sourceMaximalStalk D M) (hπD : (π : K) ∈ D) (t : ℕ → D)
    (C : UniformizerChainData π (fun n => sourceMaximalMap D M (t n)))
    (hunits : ∀ n (Q : MaximalSpectrum D), Q ≠ M →
      IsUnit (sourceMaximalMap D Q (t n))) :
    ∀ n, (C.endpoint n : K) ∈ D := by
  intro n
  induction n with
  | zero =>
      rw [C.top]
      exact D.pow_mem hπD C.exponent
  | succ n ih =>
      have hy0 : (t n : K) ≠ 0 := by
        intro hz
        apply C.ratio_ne_zero n
        apply Subtype.ext
        exact hz
      have heq : (C.endpoint (n + 1) : K) = (C.endpoint n : K) / (t n : K) := by
        apply (eq_div_iff hy0).mpr
        exact (congrArg (fun r : sourceMaximalStalk D M => (r : K)) (C.step n)).symm
      rw [heq]
      exact source_div_mem_of_stalk_and_units D M ih (t n)
        (heq ▸ (C.endpoint (n + 1)).property) (hunits n)

/-- Concrete source/stalk setup for the semilocal intersection argument. The local power-return witnesses
remain in the chosen stalk; endpoint and ratio source membership is explicit. -/
structure SemilocalChainSetup (D : Subring K) [IsFractionRing D K]
    (M : MaximalSpectrum D) where
  base : Subring K
  base_le : base ≤ sourceMaximalStalk D M
  base_dvr : IsDiscreteValuationRing base
  base_local : IsLocalHom (Subring.inclusion base_le)
  base_algebraic : Algebra.IsAlgebraic base K
  uniformizer : base
  uniformizer_irreducible : Irreducible uniformizer
  uniformizer_source : (uniformizer : K) ∈ D
  ratio : ℕ → D
  ratio_mem_chosen : ∀ n, ratio n ∈ M.asIdeal
  ratio_unit_elsewhere : ∀ n (Q : MaximalSpectrum D), Q ≠ M →
    IsUnit (sourceMaximalMap D Q (ratio n))
  chain : UniformizerChainData (Subring.inclusion base_le uniformizer)
    (fun n => sourceMaximalMap D M (ratio n))
  valuation : Valuation K ℝ≥0
  normalized : realValuationOrder valuation (uniformizer : K) = 1
  bounded : ∀ r : sourceMaximalStalk D M, valuation (r : K) ≤ 1
  centered : ∀ r : sourceMaximalStalk D M, r ≠ 0 →
    (0 < realValuationOrder valuation (r : K) ↔ ¬ IsUnit r)
  ratio_order_pos : ∀ n, 0 < realValuationOrder valuation (ratio n : K)
  endpoint_order_ge_one : ∀ n, 1 ≤ realValuationOrder valuation (chain.endpoint n : K)
  endpoint_source : ∀ n, (chain.endpoint n : K) ∈ D


/-- Failure of ACCP at an actual maximal stalk of a semilocal HA domain
supplies all source/stalk data needed before the local chain certificate.
Hereditary atomicity is used only on the original source. -/
theorem exists_semilocalChainSetup
    (D : Subring K) [IsFractionRing D K] [Finite (MaximalSpectrum D)]
    (hD : Factorization.IsHereditarilyAtomic D) (hfield : ¬ IsField D)
    (M : MaximalSpectrum D)
    (hfail : ¬ WfDvdMonoid (Localization.AtPrime M.asIdeal)) :
    Nonempty (SemilocalChainSetup D M) := by
  classical
  let R := sourceMaximalStalk D M
  let S := Localization.subalgebra.ofField K M.asIdeal.primeCompl
    M.asIdeal.primeCompl_le_nonZeroDivisors
  let : Algebra D R := inferInstanceAs (Algebra D S)
  let : IsLocalization.AtPrime R M.asIdeal :=
    inferInstanceAs (IsLocalization.AtPrime S M.asIdeal)
  let : IsLocalRing R := IsLocalization.AtPrime.isLocalRing R M.asIdeal
  let : IsFractionRing R K := inferInstanceAs (IsFractionRing S K)
  obtain ⟨A, hAR, hA, hlocal, halg, π, hπ, d, _, _, hd⟩ :=
    exists_source_uniformizer_at_maximal hD hfield K M
  let : IsDiscreteValuationRing A := hA
  let : Algebra.IsAlgebraic A K := halg
  have hπD : (π : K) ∈ D := by
    change (d : K) = (π : K) at hd
    exact hd ▸ d.property
  obtain ⟨x, t, hx, _, htM, hxt, hxQ⟩ :=
    semilocal_ha_exists_source_nonunit_chain hD M hfail
  have hunit : ∀ n (Q : MaximalSpectrum D), Q ≠ M →
      IsUnit (sourceMaximalMap D Q (t n)) := by
    intro n Q hQM
    apply (isUnit_sourceMaximalMap_iff D Q (t n)).mpr
    exact sourceChain_ratio_not_mem_of_top_not_mem x t hxt Q.asIdeal (hxQ 0 Q hQM) n
  have hxR : ∀ n, sourceMaximalMap D M (x n) ≠ 0 := fun n =>
    (map_ne_zero_iff _ (Subring.inclusion_injective (le_sourceMaximalStalk D M))).mpr (hx n)
  have htR : ∀ n, sourceMaximalMap D M (t n) ∈ IsLocalRing.maximalIdeal R := by
    intro n
    apply (IsLocalRing.mem_maximalIdeal _).mpr
    intro hu
    exact ((isUnit_sourceMaximalMap_iff D M (t n)).mp hu) (htM n)
  have hxtR : ∀ n, sourceMaximalMap D M (x n) =
      sourceMaximalMap D M (x (n + 1)) * sourceMaximalMap D M (t n) := by
    intro n
    simpa only [map_mul] using congrArg (sourceMaximalMap D M) (hxt n)
  obtain ⟨C, v, hnorm, hv, hcenter, htpos, hcpos⟩ :=
    exists_valued_uniformizerChainData A R hAR π hπ
      (fun n => sourceMaximalMap D M (x n)) (fun n => sourceMaximalMap D M (t n))
      hxR htR hxtR
  exact ⟨{
    base := A
    base_le := hAR
    base_dvr := hA
    base_local := hlocal
    base_algebraic := halg
    uniformizer := π
    uniformizer_irreducible := hπ
    uniformizer_source := hπD
    ratio := t
    ratio_mem_chosen := htM
    ratio_unit_elsewhere := hunit
    chain := C
    valuation := v
    normalized := hnorm
    bounded := hv
    centered := fun r hr => (hcenter r hr).trans (IsLocalRing.mem_maximalIdeal r)
    ratio_order_pos := htpos
    endpoint_order_ge_one := hcpos
    endpoint_source := C.endpoints_mem_source D M (Subring.inclusion hAR π) hπD t hunit
  }⟩

namespace SemilocalChainSetup
variable {D : Subring K} [IsFractionRing D K] {M : MaximalSpectrum D}
    (H : SemilocalChainSetup D M)

/-- The same uniformizer as an element of the original source. -/
def sourceUniformizer : D := ⟨H.uniformizer, H.uniformizer_source⟩

/-- The actual scaled endpoints as elements of the original source. -/
def sourceEndpoint (n : ℕ) : D := ⟨H.chain.endpoint n, H.endpoint_source n⟩

theorem sourceUniformizer_ne_zero : H.sourceUniformizer ≠ 0 := by
  intro h
  apply H.uniformizer_irreducible.ne_zero
  apply Subtype.ext
  exact congrArg (fun d : D => (d : K)) h

theorem sourceEndpoint_ne_zero (n : ℕ) : H.sourceEndpoint n ≠ 0 := by
  intro h
  apply H.chain.endpoint_ne_zero n
  apply Subtype.ext
  exact congrArg (fun d : D => (d : K)) h

theorem sourceEndpoint_top : H.sourceEndpoint 0 = H.sourceUniformizer ^ H.chain.exponent := by
  apply Subtype.ext
  exact congrArg (fun r : sourceMaximalStalk D M => (r : K)) H.chain.top

theorem sourceEndpoint_step (n : ℕ) :
    H.sourceEndpoint n = H.sourceEndpoint (n + 1) * H.ratio n := by
  apply Subtype.ext
  exact congrArg (fun r : sourceMaximalStalk D M => (r : K)) (H.chain.step n)

theorem ratio_ne_zero (n : ℕ) : H.ratio n ≠ 0 := by
  intro h
  exact H.chain.ratio_ne_zero n (by rw [h, map_zero])

/-- Every finite product of the retained ratios is still a unit at every
other maximal stalk, allowing arbitrary chosen blocks later on. -/
theorem ratio_prod_isUnit_elsewhere (s : Finset ℕ) (Q : MaximalSpectrum D) (hQM : Q ≠ M) :
    IsUnit (sourceMaximalMap D Q (∏ i ∈ s, H.ratio i)) := by
  rw [map_prod]
  exact IsUnit.prod_iff.mpr fun i _ => H.ratio_unit_elsewhere i Q hQM

/-- Fresh division by any finite ratio block returns to the original source
as soon as the local chain certificate proves the chosen-stalk membership. -/
theorem div_ratio_prod_mem_source (s : Finset ℕ) {g : K} (hg : g ∈ D)
    (hchosen : g / (∏ i ∈ s, (H.ratio i : K)) ∈ sourceMaximalStalk D M) :
    g / (∏ i ∈ s, (H.ratio i : K)) ∈ D := by
  have h := source_div_mem_of_stalk_and_units D M hg (∏ i ∈ s, H.ratio i)
    (by simpa only [SubmonoidClass.coe_finsetProd] using hchosen)
    (fun Q hQM => H.ratio_prod_isUnit_elsewhere s Q hQM)
  simpa only [SubmonoidClass.coe_finsetProd] using h

/-- The original-source endpoints retain the exact uniformizer-power quotient. -/
theorem sourceEndpoint_eq_div_prod (n : ℕ) :
    (H.sourceEndpoint n : K) = (H.uniformizer : K) ^ H.chain.exponent /
      ∏ i ∈ Finset.range n, (H.ratio i : K) :=
  H.chain.map_endpoint_eq_div_prod (sourceMaximalStalk D M).subtype
    Subtype.val_injective n

/-- The chosen source uniformizer is a nonunit at the selected maximal stalk. -/
theorem sourceUniformizer_mem_chosen : H.sourceUniformizer ∈ M.asIdeal := by
  have hr0 : sourceMaximalMap D M H.sourceUniformizer ≠ 0 :=
    (map_ne_zero_iff _ (Subring.inclusion_injective (le_sourceMaximalStalk D M))).mpr
      H.sourceUniformizer_ne_zero
  have hpos : 0 < realValuationOrder H.valuation
      (sourceMaximalMap D M H.sourceUniformizer : K) := by
    change 0 < realValuationOrder H.valuation (H.uniformizer : K)
    rw [H.normalized]
    exact zero_lt_one
  have hnonunit := (H.centered _ hr0).mp hpos
  by_contra h
  exact hnonunit ((isUnit_sourceMaximalMap_iff D M H.sourceUniformizer).mpr h)

/-- Consecutive blocks of retained ratios are units at every other stalk. -/
theorem ratio_block_isUnit_elsewhere (a length : ℕ) (Q : MaximalSpectrum D) (hQM : Q ≠ M) :
    IsUnit (sourceMaximalMap D Q (∏ i ∈ Finset.range length, H.ratio (a + i))) := by
  rw [map_prod]
  exact IsUnit.prod_iff.mpr fun i _ => H.ratio_unit_elsewhere (a + i) Q hQM

/-- The source-return statement in The semilocal intersection for a fresh selected ratio block. -/
theorem div_ratio_block_mem_source (a length : ℕ) {g : K} (hg : g ∈ D)
    (hchosen : g / (∏ i ∈ Finset.range length, (H.ratio (a + i) : K)) ∈
      sourceMaximalStalk D M) :
    g / (∏ i ∈ Finset.range length, (H.ratio (a + i) : K)) ∈ D := by
  have h := source_div_mem_of_stalk_and_units D M hg
    (∏ i ∈ Finset.range length, H.ratio (a + i))
    (by simpa only [SubmonoidClass.coe_finsetProd] using hchosen)
    (fun Q hQM => H.ratio_block_isUnit_elsewhere a length Q hQM)
  simpa only [SubmonoidClass.coe_finsetProd] using h

end SemilocalChainSetup

end HereditaryAtomicity.DVRBase
