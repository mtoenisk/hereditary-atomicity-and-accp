import HereditaryAtomicity.PrueferOverring
import HereditaryAtomicity.ValuationRank
import HereditaryAtomicity.ValuationApproximation
import Mathlib.RingTheory.Spectrum.Maximal.Localization

/-!
# Actual maximal valuation branches of a one-dimensional Prüfer domain

The branches are the literal prime localizations in the specified fraction field.
Their real representatives retain the integer ring and center exactly.
-/

namespace HereditaryAtomicity

open scoped NNReal

variable {K : Type*} [Field K]

/-- The actual valuation branch at a maximal ideal of a Prüfer subring. -/
noncomputable def prueferMaximalValuation (B : Subring K) [IsFractionRing B K]
    (hB : IsPrueferDomain B) (P : MaximalSpectrum B) : ValuationSubring K := by
  let V := (LocalSubring.ofPrime B P.asIdeal).toSubring
  let : ValuationRing V := valuationRing_of_ringEquiv
    (LocalSubring.ofPrimeEquiv B P.asIdeal).symm.toRingEquiv (hB P.asIdeal)
  let : IsFractionRing V K := isFractionRing_of_subring_le B V
    (LocalSubring.le_ofPrime B P.asIdeal)
  exact valuationSubringOfIsFractionRing V

@[simp] theorem prueferMaximalValuation_toSubring (B : Subring K) [IsFractionRing B K]
    (hB : IsPrueferDomain B) (P : MaximalSpectrum B) :
    (prueferMaximalValuation B hB P).toSubring =
      (LocalSubring.ofPrime B P.asIdeal).toSubring := rfl

/-- The branch center on the original domain is exactly its indexing maximal ideal. -/
theorem prueferMaximalValuation_lt_one_iff (B : Subring K) [IsFractionRing B K]
    (hB : IsPrueferDomain B) (P : MaximalSpectrum B) (b : B) :
    (prueferMaximalValuation B hB P).valuation (b : K) < 1 ↔ b ∈ P.asIdeal := by
  let W := prueferMaximalValuation B hB P
  let bW : W := ⟨b, LocalSubring.le_ofPrime B P.asIdeal b.property⟩
  have hu : IsUnit bW ↔ b ∉ P.asIdeal :=
    IsLocalization.AtPrime.isUnit_to_map_iff
      (LocalSubring.ofPrime B P.asIdeal).toSubring P.asIdeal b
  have hv := W.valuation_le_one bW
  rw [lt_iff_le_and_ne]
  constructor
  · rintro ⟨_, hn⟩
    by_contra hnmem
    exact hn ((W.valuation_eq_one_iff bW).mp (hu.mpr hnmem))
  · intro hb
    exact ⟨hv, fun heq => hu.mp ((W.valuation_eq_one_iff bW).mpr heq) hb⟩

/-- Branches are proper when the Prüfer domain is not a field. -/
theorem prueferMaximalValuation_ne_top (B : Subring K) [IsFractionRing B K]
    (hB : IsPrueferDomain B) (hfield : ¬ IsField B) (P : MaximalSpectrum B) :
    prueferMaximalValuation B hB P ≠ ⊤ := by
  obtain ⟨b, hb, hb0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (Ring.ne_bot_of_isMaximal_of_not_isField P.isMaximal hfield)
  have hlt := (prueferMaximalValuation_lt_one_iff B hB P b).mpr hb
  intro heq
  have hunit : IsUnit (⟨(b : K), by simp⟩ : (⊤ : ValuationSubring K)) := by
    have hu : IsUnit (b : K) := isUnit_iff_ne_zero.mpr (fun h => hb0 (Subtype.ext h))
    exact hu.map (Subring.topEquiv : (⊤ : Subring K) ≃+* K).symm.toRingHom
  rw [heq] at hlt
  exact hlt.ne ((ValuationSubring.valuation_eq_one_iff ⊤ _).mp hunit)

/-- The dimension-one hypothesis constructs a rank-one valuation at every branch. -/
theorem prueferMaximalValuation_rankOne (B : Subring K) [IsFractionRing B K]
    [Ring.KrullDimLE 1 B] (hB : IsPrueferDomain B) (hfield : ¬ IsField B)
    (P : MaximalSpectrum B) : Nonempty (prueferMaximalValuation B hB P).valuation.RankOne := by
  let : Ring.KrullDimLE 1 (prueferMaximalValuation B hB P) := krullDimLE_ofPrime B P.asIdeal
  exact valuationSubring_nonempty_rankOne _ (prueferMaximalValuation_ne_top B hB hfield P)

/-- The two concrete constructions of localization inside a fraction field agree. -/
theorem ofPrime_eq_localization_ofField (B : Subring K) [IsFractionRing B K]
    (P : Ideal B) [P.IsPrime] :
    (LocalSubring.ofPrime B P).toSubring =
      (Localization.subalgebra.ofField K P.primeCompl P.primeCompl_le_nonZeroDivisors).toSubring := by
  ext x
  change x ∈ (Localization.mapToFractionRing K P.primeCompl
    (Localization.AtPrime P) P.primeCompl_le_nonZeroDivisors).range ↔ _
  exact Localization.subalgebra.mem_range_mapToFractionRing_iff_ofField K P.primeCompl
    P.primeCompl_le_nonZeroDivisors (Localization.AtPrime P) x

/-- An actual domain is the intersection of its maximal valuation branches. -/
theorem mem_pruefer_iff_mem_all_maximalValuations
    (B : Subring K) [IsFractionRing B K] (hB : IsPrueferDomain B) (x : K) :
    x ∈ B ↔ ∀ P : MaximalSpectrum B, x ∈ prueferMaximalValuation B hB P := by
  constructor
  · intro hx P
    exact LocalSubring.le_ofPrime B P.asIdeal hx
  · intro hx
    have hint : x ∈ (⨅ P : MaximalSpectrum B,
        Localization.subalgebra.ofField K P.asIdeal.primeCompl
          P.asIdeal.primeCompl_le_nonZeroDivisors) := by
      rw [Algebra.mem_iInf]
      intro P
      change x ∈ (Localization.subalgebra.ofField K P.asIdeal.primeCompl
        P.asIdeal.primeCompl_le_nonZeroDivisors).toSubring
      rw [← ofPrime_eq_localization_ofField]
      exact hx P
    rw [MaximalSpectrum.iInf_localization_eq_bot B K] at hint
    obtain ⟨b, hb⟩ := hint
    exact hb ▸ b.property

/-- Distinct maximal ideals define distinct actual valuation subrings. -/
theorem prueferMaximalValuation_injective (B : Subring K) [IsFractionRing B K]
    (hB : IsPrueferDomain B) : Function.Injective (prueferMaximalValuation B hB) := by
  intro P Q h
  apply MaximalSpectrum.ext
  ext b
  rw [← prueferMaximalValuation_lt_one_iff B hB P,
    ← prueferMaximalValuation_lt_one_iff B hB Q, h]

/-- A real representative of each proper maximal valuation branch. -/
noncomputable def prueferMaximalRealValuation (B : Subring K) [IsFractionRing B K]
    [Ring.KrullDimLE 1 B] (hB : IsPrueferDomain B) (hfield : ¬ IsField B)
    (P : MaximalSpectrum B) : Valuation K ℝ≥0 := by
  let : (prueferMaximalValuation B hB P).valuation.RankOne :=
    Classical.choice (prueferMaximalValuation_rankOne B hB hfield P)
  exact ValuationApproximation.realValuation (prueferMaximalValuation B hB P).valuation

theorem prueferMaximalRealValuation_isEquiv (B : Subring K) [IsFractionRing B K]
    [Ring.KrullDimLE 1 B] (hB : IsPrueferDomain B) (hfield : ¬ IsField B)
    (P : MaximalSpectrum B) :
    (prueferMaximalRealValuation B hB hfield P).IsEquiv
      (prueferMaximalValuation B hB P).valuation := by
  let : (prueferMaximalValuation B hB P).valuation.RankOne :=
    Classical.choice (prueferMaximalValuation_rankOne B hB hfield P)
  unfold prueferMaximalRealValuation
  exact ValuationApproximation.realValuation_isEquiv _

/-- Passing to real values preserves the actual valuation ring. -/
@[simp] theorem prueferMaximalRealValuation_valuationSubring
    (B : Subring K) [IsFractionRing B K] [Ring.KrullDimLE 1 B]
    (hB : IsPrueferDomain B) (hfield : ¬ IsField B) (P : MaximalSpectrum B) :
    (prueferMaximalRealValuation B hB hfield P).valuationSubring =
      prueferMaximalValuation B hB P := by
  simpa using (Valuation.isEquiv_iff_valuationSubring _ _).mp
    (prueferMaximalRealValuation_isEquiv B hB hfield P)

/-- These real valuations are nontrivial, independently of any discreteness. -/
theorem prueferMaximalRealValuation_isNontrivial
    (B : Subring K) [IsFractionRing B K] [Ring.KrullDimLE 1 B]
    (hB : IsPrueferDomain B) (hfield : ¬ IsField B) (P : MaximalSpectrum B) :
    (prueferMaximalRealValuation B hB hfield P).IsNontrivial := by
  let : (prueferMaximalValuation B hB P).valuation.RankOne :=
    Classical.choice (prueferMaximalValuation_rankOne B hB hfield P)
  exact (prueferMaximalRealValuation_isEquiv B hB hfield P).isNontrivial_iff.mpr inferInstance

/-- Strictly positive additive order in a branch means membership in its exact
maximal ideal; our real valuations use the equivalent multiplicative convention. -/
theorem prueferMaximalRealValuation_lt_one_iff
    (B : Subring K) [IsFractionRing B K] [Ring.KrullDimLE 1 B]
    (hB : IsPrueferDomain B) (hfield : ¬ IsField B) (P : MaximalSpectrum B) (b : B) :
    prueferMaximalRealValuation B hB hfield P (b : K) < 1 ↔ b ∈ P.asIdeal := by
  have h := (prueferMaximalRealValuation_isEquiv B hB hfield P).lt_iff_lt
    (x := (b : K)) (y := (1 : K))
  simpa only [map_one] using h.trans (prueferMaximalValuation_lt_one_iff B hB P b)

/-- A Prüfer domain of dimension at most one is the intersection of the
integer rings of its actual real-valued maximal branches. -/
theorem mem_pruefer_iff_realValuations_le_one
    (B : Subring K) [IsFractionRing B K] [Ring.KrullDimLE 1 B]
    (hB : IsPrueferDomain B) (hfield : ¬ IsField B) (x : K) :
    x ∈ B ↔ ∀ P : MaximalSpectrum B, prueferMaximalRealValuation B hB hfield P x ≤ 1 := by
  rw [mem_pruefer_iff_mem_all_maximalValuations B hB]
  apply forall_congr'
  intro P
  have heq := prueferMaximalRealValuation_valuationSubring B hB hfield P
  change x ∈ (prueferMaximalValuation B hB P).toSubring ↔ _
  rw [← heq]
  rfl

end HereditaryAtomicity
