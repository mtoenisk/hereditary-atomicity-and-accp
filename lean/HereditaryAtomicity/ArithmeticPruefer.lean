import Mathlib.RingTheory.DedekindDomain.Basic
import Mathlib.RingTheory.Localization.Integral
import Mathlib.RingTheory.Valuation.LocalSubring
import Mathlib.RingTheory.Ideal.Height
import HereditaryAtomicity.Pruefer
import HereditaryAtomicity.AlgebraicValuationClosure
import HereditaryAtomicity.PrueferOverring
import Mathlib.RingTheory.Localization.NumDen

/-!
# Arithmetic integral closures and Prüfer domains

The Prüfer predicate uses actual localizations at prime ideals. Arithmetic
cores permit arbitrary algebraic field extensions; no finite degree or finite
normalization is part of their definitions or fraction-field interface.
-/

namespace HereditaryAtomicity

section ArithmeticCore

variable (A F K : Type*) [CommRing A] [IsDomain A] [Field F] [Field K]
  [Algebra A F] [IsFractionRing A F] [Algebra A K] [Algebra F K]
  [IsScalarTower A F K] [Algebra.IsAlgebraic F K]

include F

/-- Clearing one algebraic equation gives the entire ambient field as the
fraction field of the actual integral closure, also for infinite extensions. -/
theorem arithmeticCore_isFractionRing : IsFractionRing (integralClosure A K) K := by
  let : Algebra.IsAlgebraic A K := IsFractionRing.comap_isAlgebraic_iff.mpr
    (inferInstance : Algebra.IsAlgebraic F K)
  apply integralClosure.isFractionRing_of_algebraic
  intro a ha
  apply IsFractionRing.injective A F
  apply (algebraMap F K).injective
  simpa only [map_zero, ← IsScalarTower.algebraMap_apply A F K] using ha

omit F [Field F] [Algebra A F] [IsFractionRing A F] [Algebra F K] [IsScalarTower A F K]
  [Algebra.IsAlgebraic F K] in
/-- The actual integral closure of a PID has dimension at most one. This
integral-extension statement does not require a finite normalization. -/
theorem arithmeticCore_dimensionLEOne [IsPrincipalIdealRing A] :
    Ring.DimensionLEOne (integralClosure A K) := inferInstance

end ArithmeticCore

section Embedded

variable {K : Type*} [Field K]

/-- An integrally closed overring contains the entire integral closure of
every embedded smaller arithmetic base. -/
theorem integralClosure_le_integrallyClosed_overring
    (A U : Subring K) [IsFractionRing U K] [IsIntegrallyClosed U] (hAU : A ≤ U) :
    (integralClosure A K).toSubring ≤ U := by
  let : IsIntegrallyClosedIn U K := (isIntegrallyClosed_iff_isIntegrallyClosedIn K).mp
    (inferInstance : IsIntegrallyClosed U)
  exact Subring.integralClosure_le_iff.mpr (fun a => hAU a.property)

end Embedded

section LocalArithmetic

variable (A F K : Type*) [CommRing A] [IsDomain A] [IsPrincipalIdealRing A]
  [Field F] [Field K] [Algebra A F] [IsFractionRing A F]
  [Algebra A K] [Algebra F K] [IsScalarTower A F K]

/-- A valuation dominating a local overring of a PID cannot introduce new
fractions from the base field. Reduced fractions and the local map supply
the unit denominator; algebraicity is not needed for this step. -/
theorem valuation_restriction_mem_of_local_arithmetic
    (U : LocalSubring K) (hAU : ∀ a : A, algebraMap A K a ∈ U.toSubring)
    (W : ValuationSubring K) (hUW : U ≤ W.toLocalSubring)
    (v : W.comap (algebraMap F K)) :
    algebraMap F K (v : F) ∈ U.toSubring := by
  let f : A →+* U.toSubring := (algebraMap A K).codRestrict U.toSubring hAU
  let g : U.toSubring →+* W := Subring.inclusion hUW.1
  let : IsLocalHom g := hUW.2
  let a := IsFractionRing.num A (v : F)
  let b := IsFractionRing.den A (v : F)
  have hcop : IsCoprime (g (f a)) (g (f b)) :=
    (IsFractionRing.num_den_reduced A (v : F)).isCoprime.map (g.comp f)
  have hdiv : g (f b) ∣ g (f a) := by
    refine ⟨⟨algebraMap F K (v : F), v.property⟩, ?_⟩
    apply Subtype.ext
    change algebraMap A K a = algebraMap A K b * algebraMap F K (v : F)
    rw [IsScalarTower.algebraMap_apply A F K, IsScalarTower.algebraMap_apply A F K,
      ← map_mul]
    apply congrArg (algebraMap F K)
    have heq := IsFractionRing.mk'_num_den' A (v : F)
    have hb : algebraMap A F b ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors b.property
    exact (div_eq_iff hb).mp heq |>.trans (mul_comm _ _)
  have hb : IsUnit (f (b : A)) := isUnit_of_map_unit g _
    (hcop.symm.isRelPrime.isUnit_of_dvd hdiv)
  have hmem := U.toSubring.mul_mem (hAU a) (Submonoid.inv_mem_of_isUnit hb)
  have heq : algebraMap A K a * (algebraMap A K b)⁻¹ =
      algebraMap F K (v : F) := by
    rw [IsScalarTower.algebraMap_apply A F K, IsScalarTower.algebraMap_apply A F K,
      ← map_inv₀, ← map_mul]
    exact congrArg (algebraMap F K) (by
      simpa only [div_eq_mul_inv] using IsFractionRing.mk'_num_den' A (v : F))
  exact heq ▸ hmem

/-- Every integrally closed local arithmetic overring in an arbitrary
algebraic extension is a valuation domain. -/
theorem valuationRing_of_integrallyClosed_local_arithmetic
    [Algebra.IsAlgebraic F K] (U : LocalSubring K)
    [IsFractionRing U.toSubring K] [IsIntegrallyClosed U.toSubring]
    (hAU : ∀ a : A, algebraMap A K a ∈ U.toSubring) : ValuationRing U.toSubring := by
  obtain ⟨W, hUW⟩ := U.exists_le_valuationSubring
  let V := W.comap (algebraMap F K)
  let : Algebra V K := ((algebraMap F K).comp V.subtype).toAlgebra
  let : IsScalarTower V F K := IsScalarTower.of_algebraMap_eq' rfl
  have hVU : ∀ a : V, algebraMap V K a ∈ U.toSubring :=
    valuation_restriction_mem_of_local_arithmetic A F K U hAU W hUW
  let : IsIntegrallyClosedIn U.toSubring K :=
    (isIntegrallyClosed_iff_isIntegrallyClosedIn K).mp inferInstance
  have hBU : (integralClosure V K).toSubring ≤ U.toSubring :=
    Subring.integralClosure_le_iff.mpr hVU
  have hWU : W.toSubring ≤ U.toSubring := by
    intro x hx
    obtain ⟨a, s, hs, hxs⟩ :=
      (ValuationAlgebra.mem_extension_iff_fraction_of_isAlgebraic V W rfl x).mp hx
    let sU : U.toSubring := ⟨s, hBU s.property⟩
    let g : U.toSubring →+* W := Subring.inclusion hUW.1
    let : IsLocalHom g := hUW.2
    have hsW : IsUnit (ValuationAlgebra.integralClosureToProlongation V W rfl s) :=
      IsLocalRing.notMem_maximalIdeal.mp hs
    have hsU : IsUnit sU := isUnit_of_map_unit g sU hsW
    rw [hxs, div_eq_mul_inv]
    exact U.toSubring.mul_mem (hBU a.property) (Submonoid.inv_mem_of_isUnit hsU)
  have heq : W.toSubring = U.toSubring := le_antisymm hWU hUW.1
  exact heq ▸ (inferInstanceAs (ValuationRing W) : ValuationRing W.toSubring)

end LocalArithmetic

section ArithmeticPruefer

variable (A F K : Type*) [CommRing A] [IsDomain A] [IsPrincipalIdealRing A]
  [Field F] [Field K] [Algebra A F] [IsFractionRing A F]
  [Algebra A K] [Algebra F K] [IsScalarTower A F K] [Algebra.IsAlgebraic F K]

include F

/-- An integrally closed arithmetic overring in an arbitrary algebraic
extension of the PID fraction field is Prüfer. -/
theorem isPrueferDomain_of_integrallyClosed_arithmetic
    (U : Subring K) [IsFractionRing U K] [IsIntegrallyClosed U]
    (hAU : ∀ a : A, algebraMap A K a ∈ U) : IsPrueferDomain U := by
  intro P hP
  let T := LocalSubring.ofPrime U P
  let : IsFractionRing T.toSubring K :=
    isFractionRing_of_subring_le U T.toSubring (LocalSubring.le_ofPrime U P)
  let : IsIntegrallyClosed T.toSubring :=
    isIntegrallyClosed_of_isLocalization T.toSubring P.primeCompl
      P.primeCompl_le_nonZeroDivisors
  have hT : ValuationRing T.toSubring :=
    valuationRing_of_integrallyClosed_local_arithmetic A F K T
      (fun a => LocalSubring.le_ofPrime U P (hAU a))
  exact valuationRing_of_ringEquiv (LocalSubring.ofPrimeEquiv U P).toRingEquiv hT

/-- The entire arithmetic integral closure is Prüfer even in an infinite
algebraic field extension. -/
theorem arithmeticCore_isPrueferDomain : IsPrueferDomain (integralClosure A K) := by
  let C := (integralClosure A K).toSubring
  let : IsFractionRing C K := arithmeticCore_isFractionRing A F K
  let : IsIntegrallyClosed C :=
    (isIntegrallyClosed_iff_isIntegrallyClosedIn K).mpr inferInstance
  exact isPrueferDomain_of_integrallyClosed_arithmetic A F K C
    (fun a => (integralClosure A K).algebraMap_mem a)

/-- Every integrally closed arithmetic overring has Krull dimension at most
one. The arithmetic integral closure is integral over the PID, and every
overring of that Prüfer core has no larger dimension. -/
theorem integrallyClosed_overring_dimensionLEOne_of_arithmetic
    (U : Subring K) [IsFractionRing U K] [IsIntegrallyClosed U]
    (hAU : ∀ a : A, algebraMap A K a ∈ U) : Ring.KrullDimLE 1 U := by
  let C := (integralClosure A K).toSubring
  let : IsFractionRing C K := arithmeticCore_isFractionRing A F K
  let : Ring.KrullDimLE 1 C := inferInstanceAs (Ring.KrullDimLE 1 (integralClosure A K))
  let : IsIntegrallyClosedIn U K :=
    (isIntegrallyClosed_iff_isIntegrallyClosedIn K).mp inferInstance
  have hCU : C ≤ U := Subring.integralClosure_le_iff.mpr hAU
  exact krullDimLE_one_of_pruefer_subring_le C U hCU
    (arithmeticCore_isPrueferDomain A F K)

end ArithmeticPruefer

end HereditaryAtomicity
