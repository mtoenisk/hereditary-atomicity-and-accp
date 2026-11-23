import UnconditionalCounterexample.Variations.MultiDomainExamples
import UnconditionalCounterexample.Variations.MultiDomainPointValues

/-!
# Atomic descent for the two boundary dimensions

Integer conductors are applied to the concrete order profiles, returns and
cube chains on the ordinary and upper-dimensional domains.
-/

noncomputable section
namespace UnconditionalCounterexample.Variations

open GuardSupport MultivariateSelection MultiDomain

theorem ordinaryDimensionDomain_of_conductor (r : ℕ)
    (h : ∀ T : Subring (ordinaryDimensionDomain r), ¬ Factorization.IsBFDomain T →
      ∃ m : ℕ, 0 < m ∧ ∀ z, (m : ordinaryDimensionDomain r) * z ∈ T) :
    PrescribedDimension (ordinaryDimensionDomain r) (r+1) := by
  let C := realizedChoices (r := r) reservedPrime false
  obtain ⟨_,_,hchain⟩ := ordinaryDimensionDomain_chain r
  exact ⟨ordinaryDimensionDomain_fraction r, ordinaryDimensionDomain_normal r,
    ordinaryDimensionDomain_dimension r,
    C.descent.ordinary_hereditarilyAtomic (realized_integer_return reservedPrime false) h,
    not_wf_of_strict_chain hchain⟩

theorem upperDimensionDomain_chain (r : ℕ) : ∃ t : upperDimensionDomain r,
    (t : FunctionField (r+1)) = coordinate 0 ∧ HasStrictChainAt (t^3) :=
  realized_pullback_chain (r := r) reservedPrime

theorem upperDimensionDomain_of_conductor (r : ℕ)
    (h : ∀ T : Subring (upperDimensionDomain r), ¬ Factorization.IsBFDomain T →
      ∃ m : ℕ, 0 < m ∧ ∀ z, (m : upperDimensionDomain r) * z ∈ T) :
    PrescribedDimension (upperDimensionDomain r) (r+2) := by
  let C := realizedChoices (r := r) reservedPrime true
  obtain ⟨_,_,hchain⟩ := upperDimensionDomain_chain r
  exact ⟨upperDimensionDomain_fraction r, upperDimensionDomain_normal r,
    upperDimensionDomain_dimension r,
    C.descent.pullback_hereditarilyAtomic (actualData r true) (flagPoint r) (flagPoint_retained (actualLocal r true))
      reservedPrime.val (realized_moving_point_unit reservedPrime) (realized_integer_return reservedPrime true)
      (realized_point_return reservedPrime) h,
    not_wf_of_strict_chain hchain⟩

end UnconditionalCounterexample.Variations
