import HereditaryAtomicity.SemilocalDimension
import Mathlib.RingTheory.DiscreteValuationRing.Basic

/-!
# Dimension and radical return over a DVR

Algebraicity over the DVR fraction field controls the radical of a uniformizer-power
ideal. The dimension bound descends from the integral normalization and applies to
arbitrary algebraic extensions.
-/

noncomputable section

namespace HereditaryAtomicity.DVRBase

section General

variable (A R K : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [CommRing R] [IsDomain R] [Field K]
  [Algebra A R] [Algebra R K] [IsFractionRing R K]
  [Algebra A K] [IsScalarTower A R K] [FaithfulSMul A K]
  [Algebra.IsAlgebraic A K]

include A K

/-- A domain algebraic over an embedded DVR has dimension at most one. -/
theorem dimensionLE_one_of_algebraic_dvr : Ring.KrullDimLE 1 R := by
  let F := FractionRing A
  let : Algebra F K := FractionRing.liftAlgebra A K
  let : IsScalarTower A F K := FractionRing.isScalarTower_liftAlgebra A K
  let : Algebra.IsAlgebraic F K := IsFractionRing.comap_isAlgebraic_iff.mp
    (inferInstance : Algebra.IsAlgebraic A K)
  let U := (integralClosure R K).toSubring
  let : IsFractionRing U K := normalization_isFractionRing R K
  let : IsIntegrallyClosed U :=
    (isIntegrallyClosed_iff_isIntegrallyClosedIn K).mpr inferInstance
  have hAU : ∀ a : A, algebraMap A K a ∈ U := by
    intro a
    rw [IsScalarTower.algebraMap_apply A R K]
    exact (integralClosure R K).algebraMap_mem (algebraMap A R a)
  let : Ring.KrullDimLE 1 (integralClosure R K) :=
    integrallyClosed_overring_dimensionLEOne_of_arithmetic A F K U hAU
  exact krullDimLE_one_of_integralClosure R K (IsFractionRing.injective R K)

/-- Every proper nonzero ideal in a local domain algebraic over an embedded
DVR has radical equal to the actual maximal ideal. -/
theorem radical_eq_maximalIdeal_of_algebraic_dvr [IsLocalRing R]
    (I : Ideal R) (hI0 : I ≠ ⊥) (hI1 : I ≠ ⊤) :
    I.radical = IsLocalRing.maximalIdeal R := by
  let : Ring.KrullDimLE 1 R := dimensionLE_one_of_algebraic_dvr A R K
  apply le_antisymm
  · exact (inferInstance : (IsLocalRing.maximalIdeal R).IsPrime).radical_le_iff.mpr
      (IsLocalRing.le_maximalIdeal hI1)
  · rw [Ideal.radical_eq_sInf]
    apply le_sInf
    rintro P ⟨hIP, hP⟩
    have hP0 : P ≠ ⊥ := fun heq => hI0 (bot_unique (heq ▸ hIP))
    exact (IsLocalRing.eq_maximalIdeal (hP.isMaximal_of_ne_bot hP0)).ge

/-- An element of the local maximal ideal has a positive power in every
nonzero ideal; in particular, the returned exponent cannot be zero. -/
theorem exists_pos_pow_mem_of_algebraic_dvr [IsLocalRing R]
    (I : Ideal R) (hI0 : I ≠ ⊥) {x : R}
    (hx : x ∈ IsLocalRing.maximalIdeal R) :
    ∃ n : ℕ, 0 < n ∧ x ^ n ∈ I := by
  by_cases hI1 : I = ⊤
  · exact ⟨1, Nat.zero_lt_one, by simp [hI1]⟩
  have hxrad : x ∈ I.radical := by
    rw [radical_eq_maximalIdeal_of_algebraic_dvr A R K I hI0 hI1]
    exact hx
  obtain ⟨n, hn⟩ := Ideal.mem_radical_iff.mp hxrad
  refine ⟨n, Nat.pos_of_ne_zero ?_, hn⟩
  intro hzero
  apply hI1
  apply Ideal.eq_top_of_isUnit_mem I _ (isUnit_one : IsUnit (1 : R))
  simpa only [hzero, pow_zero] using hn

end General

section Embedded

variable {K : Type*} [Field K] (A R : Subring K)
  [IsDiscreteValuationRing A] [IsFractionRing R K]
  [Algebra.IsAlgebraic A K] (hAR : A ≤ R)

include A hAR

/-- The dimension bound for literal subrings of the same fraction field. -/
theorem embedded_dimensionLE_one_of_algebraic_dvr : Ring.KrullDimLE 1 R := by
  let : Algebra A R := (Subring.inclusion hAR).toAlgebra
  let : IsScalarTower A R K := IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact dimensionLE_one_of_algebraic_dvr A R K

/-- Positive-power return for literal DVR and source subrings. -/
theorem embedded_exists_pos_pow_mem_of_algebraic_dvr [IsLocalRing R]
    (I : Ideal R) (hI0 : I ≠ ⊥) {x : R}
    (hx : x ∈ IsLocalRing.maximalIdeal R) :
    ∃ n : ℕ, 0 < n ∧ x ^ n ∈ I := by
  let : Algebra A R := (Subring.inclusion hAR).toAlgebra
  let : IsScalarTower A R K := IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact exists_pos_pow_mem_of_algebraic_dvr A R K I hI0 hx

end Embedded

end HereditaryAtomicity.DVRBase
