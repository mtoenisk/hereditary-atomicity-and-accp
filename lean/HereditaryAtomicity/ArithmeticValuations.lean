import HereditaryAtomicity.SemilocalArithmetic
import HereditaryAtomicity.ArithmeticPruefer
import HereditaryAtomicity.ValuationRank
import Mathlib.Algebra.Algebra.ZMod
import Mathlib.Algebra.Field.ZMod
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.RingTheory.Valuation.LocalSubring
import Mathlib.RingTheory.PrincipalIdealDomain

/-!
# Arithmetic dimension of arbitrary valuation rings

The valuation rings considered here need not contain the original domain.
Finite coefficient fields lie in every valuation ring; one of a rational
parameter and its inverse then gives a polynomial arithmetic base inside it.
-/

noncomputable section

namespace HereditaryAtomicity

open scoped IntermediateField.algebraAdjoinAdjoin

/-- Every valuation ring contains the image of a finite coefficient field. -/
theorem finiteField_algebraMap_mem_valuationSubring
    (k : Type*) [Field k] [Finite k] {K : Type*} [Field K] [Algebra k K]
    (W : ValuationSubring K) (a : k) : algebraMap k K a ∈ W := by
  have ha : IsIntegral ℤ a := IsIntegral.of_finite ℤ a
  have haK : IsIntegral ℤ (algebraMap k K a) :=
    map_isIntegral_int (algebraMap k K) ha
  exact Subring.isIntegrallyClosed_iff.mp (inferInstance : IsIntegrallyClosed W)
    haK.tower_top

/-- Inverting the generator does not change a simple intermediate field. -/
theorem intermediateField_adjoin_inv_eq
    (k : Type*) [Field k] {K : Type*} [Field K] [Algebra k K] (t : K) :
    IntermediateField.adjoin k {t⁻¹} = IntermediateField.adjoin k {t} := by
  apply le_antisymm
  · rw [IntermediateField.adjoin_le_iff, Set.singleton_subset_iff]
    exact (IntermediateField.adjoin k {t}).inv_mem
      (IntermediateField.subset_adjoin k _ (Set.mem_singleton _))
  · rw [IntermediateField.adjoin_le_iff, Set.singleton_subset_iff]
    change t ∈ IntermediateField.adjoin k {t⁻¹}
    simpa only [inv_inv] using (IntermediateField.adjoin k {t⁻¹}).inv_mem
      (IntermediateField.subset_adjoin k _ (Set.mem_singleton _))

/-- If a parameter belongs to a valuation ring, its polynomial subring does
as well; finiteness is used only for the coefficient field. -/
theorem adjoin_le_valuationSubring_of_finiteField
    (k : Type*) [Field k] [Finite k] {K : Type*} [Field K] [Algebra k K]
    (W : ValuationSubring K) {t : K} (ht : t ∈ W) :
    (Algebra.adjoin k {t}).toSubring ≤ W.toSubring := by
  let U : Subalgebra k K :=
    { W.toSubring with
      algebraMap_mem' := finiteField_algebraMap_mem_valuationSubring k W }
  have hU : Algebra.adjoin k {t} ≤ U :=
    Algebra.adjoin_le (Set.singleton_subset_iff.mpr ht)
  exact hU

/-- A simple transcendental parameter can be chosen inside each valuation
ring without changing the field over which the ambient field is algebraic. -/
theorem exists_transcendental_parameter_mem_valuationSubring
    (k : Type*) [Field k] {K : Type*} [Field K] [Algebra k K]
    (t : K) (ht : Transcendental k t)
    [Algebra.IsAlgebraic (IntermediateField.adjoin k {t}) K]
    (W : ValuationSubring K) :
    ∃ s : K, s ∈ W ∧ Transcendental k s ∧
      Algebra.IsAlgebraic (IntermediateField.adjoin k {s}) K := by
  rcases W.mem_or_inv_mem t with h | h
  · exact ⟨t, h, ht, inferInstance⟩
  · refine ⟨t⁻¹, h, fun halg => ht (IsAlgebraic.inv_iff.mp halg), ?_⟩
    rw [intermediateField_adjoin_inv_eq k t]
    infer_instance

/-- Every valuation ring of an algebraic extension of Q has dimension at
most one. The valuation ring is not required to contain any specified domain. -/
theorem valuationSubring_dimensionLEOne_of_algebraic_rat
    {K : Type*} [Field K] [CharZero K] [Algebra ℚ K]
    [Algebra.IsAlgebraic ℚ K] (W : ValuationSubring K) :
    Ring.KrullDimLE 1 W := by
  let : IsFractionRing W.toSubring K := inferInstanceAs (IsFractionRing W K)
  exact integrallyClosed_overring_dimensionLEOne_of_arithmetic ℤ ℚ K
    W.toSubring (fun a => intCast_mem W a)

/-- Every valuation ring in an algebraic extension of a one-variable field
over a finite field has dimension at most one. There is no centering premise. -/
theorem valuationSubring_dimensionLEOne_of_algebraic_adjoin_finiteField
    (k : Type*) [Field k] [Finite k] {K : Type*} [Field K] [Algebra k K]
    (t : K) (ht : Transcendental k t)
    [Algebra.IsAlgebraic (IntermediateField.adjoin k {t}) K]
    (W : ValuationSubring K) : Ring.KrullDimLE 1 W := by
  let : IsFractionRing W.toSubring K := inferInstanceAs (IsFractionRing W K)
  obtain ⟨s, hsW, hs, halg⟩ :=
    exists_transcendental_parameter_mem_valuationSubring k t ht W
  let := halg
  let := adjoin_transcendental_isPrincipalIdealRing k s hs
  exact integrallyClosed_overring_dimensionLEOne_of_arithmetic
    (Algebra.adjoin k {s}) (IntermediateField.adjoin k {s}) K W.toSubring
    (fun a => adjoin_le_valuationSubring_of_finiteField k W hsW a.property)

/-- Every valuation ring of the actual fraction field of a nonfield semilocal
HA domain has dimension at most one, including the outside valuation rings. -/
theorem valuationSubring_dimensionLEOne_of_semilocal_hereditarilyAtomic
    {R : Type*} [CommRing R] [IsDomain R] [Finite (MaximalSpectrum R)]
    (hR : Factorization.IsHereditarilyAtomic R) (hfield : ¬ IsField R)
    (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
    (W : ValuationSubring K) : Ring.KrullDimLE 1 W := by
  obtain hzero | ⟨p, hp, hchar⟩ := CharP.exists' R
  · let := hzero
    let : CharZero K := IsFractionRing.charZero_of_isFractionRing R
    let : Algebra ℚ K := DivisionRing.toRatAlgebra
    let := semilocal_fractionField_isAlgebraic_rat hR K
    exact valuationSubring_dimensionLEOne_of_algebraic_rat W
  · let := hp
    let := hchar
    let : CharP K p := IsFractionRing.charP_of_isFractionRing R p
    let : Algebra (ZMod p) R := ZMod.algebra R p
    let : Algebra (ZMod p) K := ZMod.algebra K p
    let : IsScalarTower (ZMod p) R K :=
      IsScalarTower.of_algebraMap_eq fun a => RingHom.congr_fun
        (Subsingleton.elim (algebraMap (ZMod p) K)
          ((algebraMap R K).comp (algebraMap (ZMod p) R))) a
    obtain ⟨c, hc0, hc⟩ := exists_nonzero_mem_jacobson_of_semilocal_nonfield R hfield
    have ht : Transcendental (ZMod p) (algebraMap R K c) :=
      (transcendental_algebraMap_iff (IsFractionRing.injective R K)).mpr
        (transcendental_of_nonzero_mem_jacobson (ZMod p) hc0 hc)
    let := fractionField_isAlgebraic_adjoin_jacobson (ZMod p) hR K hc0 hc
    exact valuationSubring_dimensionLEOne_of_algebraic_adjoin_finiteField
      (ZMod p) (algebraMap R K c) ht W

/-- A proper valuation ring of the fraction field of a nonfield semilocal
HA domain admits a rank-one canonical valuation. -/
theorem valuationSubring_rankOne_of_semilocal_hereditarilyAtomic
    {R : Type*} [CommRing R] [IsDomain R] [Finite (MaximalSpectrum R)]
    (hR : Factorization.IsHereditarilyAtomic R) (hfield : ¬ IsField R)
    (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
    (W : ValuationSubring K) (hW : W ≠ ⊤) : Nonempty W.valuation.RankOne := by
  let := valuationSubring_dimensionLEOne_of_semilocal_hereditarilyAtomic hR hfield K W
  exact valuationSubring_nonempty_rankOne W hW

end HereditaryAtomicity
