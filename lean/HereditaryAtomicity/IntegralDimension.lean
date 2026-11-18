import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.IntegralClosure.IntegralRestrict

/-!
# Dimension descent along injective integral maps

A nonzero prime downstairs has a nonzero prime above it. If every nonzero prime
upstairs is maximal, integral contraction makes the original prime maximal.
-/

namespace HereditaryAtomicity

/-- Dimension at most one descends along an injective integral map of domains. -/
theorem krullDimLE_one_of_integral_injective
    {R S : Type*} [CommRing R] [CommRing S] [IsDomain R] [IsDomain S]
    [Algebra R S] [Algebra.IsIntegral R S] [Ring.KrullDimLE 1 S]
    (hinj : Function.Injective (algebraMap R S)) : Ring.KrullDimLE 1 R := by
  apply Ring.KrullDimLE.mk₁'
  intro P hP0 hP
  let : P.IsPrime := hP
  have hker : RingHom.ker (algebraMap R S) = ⊥ :=
    (RingHom.injective_iff_ker_eq_bot _).mp hinj
  obtain ⟨Q, hQ, hQP⟩ := Ideal.exists_ideal_over_prime_of_isIntegral_of_isDomain
    (S := S) P (by rw [hker]; exact bot_le)
  let : Q.IsPrime := hQ
  have hQ0 : Q ≠ ⊥ := by
    intro h
    apply hP0
    rw [← hQP, h]
    exact Ideal.comap_bot_of_injective (algebraMap R S) hinj
  let : Q.IsMaximal := hQ.isMaximal_of_ne_bot hQ0
  exact hQP ▸ (inferInstance : (Q.under R).IsMaximal)

/-- The dimension bound of the entire integral closure descends to the original
embedded domain, with no finiteness condition on the normalization. -/
theorem krullDimLE_one_of_integralClosure
    (R K : Type*) [CommRing R] [IsDomain R] [Field K] [Algebra R K]
    [Ring.KrullDimLE 1 (integralClosure R K)]
    (hinj : Function.Injective (algebraMap R K)) : Ring.KrullDimLE 1 R := by
  apply krullDimLE_one_of_integral_injective (S := integralClosure R K)
  intro a b hab
  apply hinj
  exact congrArg (fun x : integralClosure R K => (x : K)) hab

end HereditaryAtomicity
