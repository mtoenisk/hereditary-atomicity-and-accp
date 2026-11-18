import Mathlib.RingTheory.Valuation.LocalSubring
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

/-!
# Actual valuation centers on an embedded normalization

A maximal ideal of an actual subring of a field is the exact contraction of the
nonunits of a containing valuation ring. The dimension-one normalization wrapper
applies this to every nonzero prime, without any value-group or rank hypothesis.
-/

namespace HereditaryAtomicity

universe u v

/-- Every maximal ideal of an actual subring has a containing valuation ring
whose nonunits contract to precisely that ideal. -/
theorem exists_valuationSubring_centered_at_maximal
    {K : Type v} [Field K] (A : Subring K) (P : Ideal A) [P.IsMaximal] :
    ∃ W : ValuationSubring K, A ≤ W.toSubring ∧
      ∀ a : A, ((a : K) ∈ W.nonunits ↔ a ∈ P) := by
  obtain ⟨W, hAW, hP⟩ := Ideal.image_subset_nonunits_valuationSubring P
    (inferInstance : P.IsMaximal).ne_top
  let f : A →+* W := Subring.inclusion hAW
  let Q : Ideal A := (IsLocalRing.maximalIdeal W).comap f
  have hQ : Q ≠ ⊤ := Ideal.comap_ne_top f (IsLocalRing.maximalIdeal.isMaximal W).ne_top
  have hPQ : P ≤ Q := by
    intro a ha
    exact W.coe_mem_nonunits_iff.mp (hP ⟨a, ha, rfl⟩)
  have hQP : Q = P := (Ideal.IsMaximal.eq_of_le (inferInstance : P.IsMaximal) hQ hPQ).symm
  refine ⟨W, hAW, fun a => ?_⟩
  rw [← hQP]
  exact W.coe_mem_nonunits_iff (a := f a)

/-- Every nonzero prime of a dimension-at-most-one actual normalization is
realized as the exact center of a valuation subring of the fraction field. -/
theorem exists_valuationSubring_centered_at_normalization_prime
    (R : Type u) [CommRing R] [IsDomain R]
    (K : Type v) [Field K] [Algebra R K] [IsFractionRing R K]
    [Ring.KrullDimLE 1 (integralClosure R K)]
    (P : Ideal (integralClosure R K)) [P.IsPrime] (hP : P ≠ ⊥) :
    ∃ W : ValuationSubring K, (integralClosure R K).toSubring ≤ W.toSubring ∧
      ∀ b : integralClosure R K, ((b : K) ∈ W.nonunits ↔ b ∈ P) := by
  let : P.IsMaximal := (inferInstance : P.IsPrime).isMaximal_of_ne_bot hP
  exact exists_valuationSubring_centered_at_maximal (integralClosure R K).toSubring P

end HereditaryAtomicity
