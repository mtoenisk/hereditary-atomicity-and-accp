import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.RingTheory.LocalProperties.IntegrallyClosed
import UnconditionalCounterexample.PaperAtomicity

/-!
# The one-dimensional instance of the prescribed-dimension theorem

The original paper domain has dimension one and is normal since its
maximal localizations are DVRs. Transporting the inclusion along the
one-variable fraction-field equivalence puts the example in the exact
ambient field used for the multivariate construction.
-/

noncomputable section

namespace UnconditionalCounterexample.Variations

/-- The rational function field in the statement of §9.1. -/
abbrev FunctionField (r : ℕ) := FractionRing (MvPolynomial (Fin r) ℚ)

/-- The requirements on a single embedded domain, with its intrinsic
factorization predicates and its inclusion into the indicated fraction field. -/
def PrescribedDimension {r : ℕ} (D : Subring (FunctionField r)) (d : ℕ) : Prop :=
  IsFractionRing D (FunctionField r) ∧ IsIntegrallyClosed D ∧ ringKrullDim D = d ∧
    Factorization.IsHereditarilyAtomic D ∧ ¬ WfDvdMonoid D

theorem normal_of_almostDedekind {R : Type*} [CommRing R] [IsDomain R]
    (h : IsAlmostDedekindDomain R) : IsIntegrallyClosed R := by
  apply IsIntegrallyClosed.of_localization_maximal
  intro M _ hM
  let := h M
  infer_instance

theorem dimension_one_of_almostDedekind {R : Type*} [CommRing R] [IsDomain R]
    (h : IsAlmostDedekindDomain R) : ringKrullDim R = 1 := by
  obtain ⟨M, hM⟩ := Ideal.exists_maximal R
  let := h M
  apply le_antisymm
  · have hle : Ring.KrullDimLE 1 R := by
      apply Ring.krullDimLE_of_isLocalization_maximal (fun P _ => Localization.AtPrime P)
      intro P hP
      let := h P
      exact Ring.krullDimLE_iff.mpr (IsDiscreteValuationRing.ringKrullDim_eq_one _).le
    exact Ring.krullDimLE_iff.mp hle
  · have hdim := IsDiscreteValuationRing.ringKrullDim_eq_one (Localization.AtPrime M)
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height M (Localization.AtPrime M)] at hdim
    rw [← hdim]
    exact Ideal.height_le_ringKrullDim_of_ne_top hM.ne_top

private def oneVariableEquiv : RatFunc ℚ ≃+* FunctionField 1 :=
  IsFractionRing.ringEquivOfRingEquiv (MvPolynomial.uniqueAlgEquiv ℚ (Fin 1)).symm.toRingEquiv

/-- A named witness for the boundary case `r=d=1`. -/
def oneDimensionalDomain : Subring (FunctionField 1) :=
  PaperConstruction.domain.map oneVariableEquiv.toRingHom

/-- For one variable, all five assertions hold on the image of the paper domain. -/
theorem oneDimensionalDomain_spec : PrescribedDimension oneDimensionalDomain 1 := by
  let := PaperConstruction.fractionRing
  let := normal_of_almostDedekind PaperConstruction.isAlmostDedekindDomain
  let e : PaperConstruction.domain ≃+* oneDimensionalDomain :=
    PaperConstruction.domain.equivMapOfInjective _ oneVariableEquiv.injective
  refine ⟨?_, IsIntegrallyClosed.of_equiv e, ?_,
    (Factorization.isHereditarilyAtomic_ringEquiv_iff e).mpr PaperConstruction.hereditarilyAtomic,
    fun h => PaperConstruction.not_wfDvdMonoid (Factorization.wfDvdMonoid_of_ringEquiv e h)⟩
  · apply IsFractionRing.of_field
    intro z
    obtain ⟨x, y, _, hxy⟩ := IsFractionRing.div_surjective PaperConstruction.domain
      (oneVariableEquiv.symm z)
    refine ⟨e x, e y, ?_⟩
    change z = oneVariableEquiv (x : RatFunc ℚ) / oneVariableEquiv (y : RatFunc ℚ)
    rw [← map_div₀]
    exact (oneVariableEquiv.symm_apply_eq.mp hxy.symm)
  · rw [← ringKrullDim_eq_of_ringEquiv e]
    simpa using dimension_one_of_almostDedekind PaperConstruction.isAlmostDedekindDomain

end UnconditionalCounterexample.Variations
