import HereditaryAtomicity.ArithmeticValuations
import HereditaryAtomicity.SemilocalCardinality
import HereditaryAtomicity.FiniteValuationApproximation
import HereditaryAtomicity.HereditaryTransfer
import HereditaryAtomicity.FractionFieldImage
import HereditaryAtomicity.Fields
import Mathlib.Algebra.Field.Equiv

/-!
# Outside finite support and hereditary transfer for semilocal HA domains

The arithmetic rank-one theorem, nonzero Jacobson radical, finite approximation
and convergent-fan theorem discharge all geometric hypotheses of factor-count
descent. The field case uses the separate hereditary field theorem.
-/

namespace HereditaryAtomicity

variable {K : Type*} [Field K]

private theorem ne_top_of_outside {D : Subring K} {V : ValuationSubring K}
    (hV : ¬ D ≤ V.toSubring) : V ≠ ⊤ := by
  intro h
  exact hV (h ▸ le_top)

/-- Every actual outside valuation of a nonfield semilocal HA domain is a DVR. -/
theorem semilocal_outside_isDiscreteValuationRing
    (D : Subring K) [IsFractionRing D K] [Finite (MaximalSpectrum D)]
    (hD : Factorization.IsHereditarilyAtomic D) (hfield : ¬ IsField D)
    (V : ValuationSubring K) (hV : ¬ D ≤ V.toSubring) : IsDiscreteValuationRing V := by
  let : V.valuation.RankOne := Classical.choice
    (valuationSubring_rankOne_of_semilocal_hereditarilyAtomic hD hfield K V
      (ne_top_of_outside hV))
  obtain ⟨j, hj0, hj⟩ := exists_nonzero_mem_jacobson_of_semilocal_nonfield D hfield
  apply outside_valuationSubring_isDiscreteValuationRing hD V hj hj0
  obtain ⟨d, hd, hdV⟩ := SetLike.not_le_iff_exists.mp hV
  exact ⟨⟨d, hd⟩, hdV⟩

/-- The required finite unit approximation is constructed from semilocal HA. -/
theorem semilocal_hasFiniteOutsideUnitApproximation
    (D : Subring K) [IsFractionRing D K] [Finite (MaximalSpectrum D)]
    (hD : Factorization.IsHereditarilyAtomic D) (hfield : ¬ IsField D) :
    HasFiniteOutsideUnitApproximation D := by
  obtain ⟨j, hj0, hj⟩ := exists_nonzero_mem_jacobson_of_semilocal_nonfield D hfield
  apply hasFiniteOutsideUnitApproximation_of_jacobson D hD hj hj0
  intro V hV
  exact valuationSubring_rankOne_of_semilocal_hereditarilyAtomic hD hfield K V
    (ne_top_of_outside hV)

/-- A fixed nonzero fraction has only finitely many positive outside values. -/
theorem semilocal_finite_positiveOutsideSupport
    (D : Subring K) [IsFractionRing D K] [Finite (MaximalSpectrum D)]
    (hD : Factorization.IsHereditarilyAtomic D) (hfield : ¬ IsField D)
    {z : K} (hz : z ≠ 0) : (positiveOutsideSupport D z).Finite := by
  let : Countable K := countable_fractionField_of_semilocal_hereditarilyAtomic_nonfield
    hD hfield K
  exact finite_outside_nonunits hD (semilocal_hasFiniteOutsideUnitApproximation D hD hfield) hz

/-- For a fixed nonzero fraction, only finitely many outside valuation rings have nonzero
additive value, counting both zeros and poles. -/
theorem semilocal_finite_outside_value_support
    (D : Subring K) [IsFractionRing D K] [Finite (MaximalSpectrum D)]
    (hD : Factorization.IsHereditarilyAtomic D) (hfield : ¬ IsField D)
    {z : K} (hz : z ≠ 0) :
    Set.Finite {W : ValuationSubring K | ¬ D ≤ W.toSubring ∧ W.valuation z ≠ 1} := by
  let : Countable K := countable_fractionField_of_semilocal_hereditarilyAtomic_nonfield
    hD hfield K
  exact finite_outside_value_ne_one hD (semilocal_hasFiniteOutsideUnitApproximation D hD hfield) hz

/-- Each nontrivial valuation of any embedded base field has finitely many
outside prolongations. No global-field or finite-degree premise is needed. -/
theorem semilocal_finite_outside_extensionFiber
    (D : Subring K) [IsFractionRing D K] [Finite (MaximalSpectrum D)]
    (hD : Factorization.IsHereditarilyAtomic D) (hfield : ¬ IsField D)
    {F : Type*} [Field F] (f : F →+* K) (V : ValuationSubring F) (hV : V ≠ ⊤) :
    Set.Finite {W : ValuationSubring K | ¬ D ≤ W.toSubring ∧ W.comap f = V} := by
  let : Countable K := countable_fractionField_of_semilocal_hereditarilyAtomic_nonfield
    hD hfield K
  exact finite_outside_extensionFiber hD
    (semilocal_hasFiniteOutsideUnitApproximation D hD hfield) f V hV

/-- One bound for a fixed nonzero product bounds occurrences of ambient units among the
nonunit factors in every unital subring. -/
theorem semilocal_uniform_ambientUnitFactorBound
    (D : Subring K) [IsFractionRing D K] [Finite (MaximalSpectrum D)]
    (hD : Factorization.IsHereditarilyAtomic D) (hfield : ¬ IsField D)
    (z : K) (hz : z ≠ 0) :
    ∃ bound : ℕ, ∀ (S : Subring K) (hSD : S ≤ D) (x : S), (x : K) = z →
      ∀ t : Multiset S, (∀ a ∈ t, ¬ IsUnit a) → Associated t.prod x →
        Factorization.ambientUnitFactorCount (Subring.inclusion hSD).toMonoidHom t ≤ bound :=
  exists_uniform_ambientUnitFactorBound_of_finite_discrete_outside D
    (semilocal_outside_isDiscreteValuationRing D hD hfield) z hz
    (semilocal_finite_positiveOutsideSupport D hD hfield hz)

/-- BF is hereditary in a nonfield semilocal HA domain. -/
theorem semilocal_subring_hereditarilyBF
    (D : Subring K) [IsFractionRing D K] [Finite (MaximalSpectrum D)]
    (hD : Factorization.IsHereditarilyAtomic D) (hfield : ¬ IsField D)
    (hBF : Factorization.IsBFDomain D) : Factorization.IsHereditarilyBF D :=
  hereditarilyBF_of_finite_discrete_outside D
    (semilocal_outside_isDiscreteValuationRing D hD hfield)
    (fun _ hz => semilocal_finite_positiveOutsideSupport D hD hfield hz) hBF

/-- ACCP is hereditary in a nonfield semilocal HA domain. -/
theorem semilocal_subring_hereditarilyACCP
    (D : Subring K) [IsFractionRing D K] [Finite (MaximalSpectrum D)]
    (hD : Factorization.IsHereditarilyAtomic D) (hfield : ¬ IsField D)
    (hACCP : WfDvdMonoid D) : Factorization.IsHereditarilyACCP D :=
  hereditarilyACCP_of_finite_discrete_outside D
    (semilocal_outside_isDiscreteValuationRing D hD hfield)
    (fun _ hz => semilocal_finite_positiveOutsideSupport D hD hfield hz) hACCP

/-- The semilocal BF transfer for arbitrary domains, including the field case. -/
theorem semilocal_hereditarilyBF {R : Type*} [CommRing R] [IsDomain R]
    [Finite (MaximalSpectrum R)] (hR : Factorization.IsHereditarilyAtomic R)
    (hBF : Factorization.IsBFDomain R) : Factorization.IsHereditarilyBF R := by
  classical
  by_cases hfield : IsField R
  · let := hfield.toField
    exact field_hereditarilyBF hR
  · let L := FractionRing R
    let D := (algebraMap R L).range
    let : IsFractionRing D L := isFractionRing_fractionImage R L
    let : Finite (MaximalSpectrum D) := finite_maximalSpectrum_fractionImage R L
    let e : R ≃+* D := fractionImageEquiv R L
    have hD : Factorization.IsHereditarilyAtomic D := hereditarilyAtomic_fractionImage R L hR
    have hDf : ¬ IsField D := fun h => hfield (e.toMulEquiv.isField_congr.mpr h)
    apply (Factorization.isHereditarilyBF_ringEquiv_iff e).mp
    exact semilocal_subring_hereditarilyBF D hD hDf
      ((Factorization.isBFDomain_ringEquiv_iff e).mpr hBF)

/-- The semilocal ACCP transfer for arbitrary domains, including fields. -/
theorem semilocal_hereditarilyACCP {R : Type*} [CommRing R] [IsDomain R]
    [Finite (MaximalSpectrum R)] (hR : Factorization.IsHereditarilyAtomic R)
    (hACCP : WfDvdMonoid R) : Factorization.IsHereditarilyACCP R := by
  classical
  by_cases hfield : IsField R
  · let := hfield.toField
    exact field_hereditarilyACCP hR
  · let L := FractionRing R
    let D := (algebraMap R L).range
    let : IsFractionRing D L := isFractionRing_fractionImage R L
    let : Finite (MaximalSpectrum D) := finite_maximalSpectrum_fractionImage R L
    let e : R ≃+* D := fractionImageEquiv R L
    have hD : Factorization.IsHereditarilyAtomic D := hereditarilyAtomic_fractionImage R L hR
    have hDf : ¬ IsField D := fun h => hfield (e.toMulEquiv.isField_congr.mpr h)
    apply (Factorization.isHereditarilyACCP_ringEquiv_iff e).mp
    exact semilocal_subring_hereditarilyACCP D hD hDf
      ((Factorization.wfDvdMonoid_ringEquiv_iff e).mpr hACCP)

end HereditaryAtomicity
