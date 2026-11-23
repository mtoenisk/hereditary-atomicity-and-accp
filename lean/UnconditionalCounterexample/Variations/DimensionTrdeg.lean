import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.RingTheory.Localization.FractionRing

/-!
# Absolute transcendence degree of the prescribed fraction fields

Use the coordinate transcendence basis over the rationals and the algebraic
extensions from a domain to its fraction field and from the integers to the
rationals. This gives the degree also for the domain itself over ℤ.
-/

namespace UnconditionalCounterexample.Variations

open Algebra
open scoped nonZeroDivisors

/-- The fraction field of the polynomial ring in `r` rational variables has
absolute transcendence degree `r`. -/
theorem rationalFunctionField_trdeg (r : ℕ) :
    trdeg ℚ (FractionRing (MvPolynomial (Fin r) ℚ)) = r := by
  let P := MvPolynomial (Fin r) ℚ
  let K := FractionRing P
  let : Algebra.IsAlgebraic P K := IsLocalization.isAlgebraic K P⁰
  have hb : IsTranscendenceBasis ℚ (algebraMap P K ∘ MvPolynomial.X (σ := Fin r)) :=
    (IsTranscendenceBasis.mvPolynomial (Fin r) ℚ).algebraMap_comp
  simpa using hb.cardinalMk_eq_trdeg.symm

/-- An actual subring with this fraction field has absolute transcendence degree `r`
over the integers as well. -/
theorem subring_trdeg_of_fractionRing (r : ℕ)
    (D : Subring (FractionRing (MvPolynomial (Fin r) ℚ)))
    [IsFractionRing D (FractionRing (MvPolynomial (Fin r) ℚ))] :
    trdeg ℤ D = r := by
  let K := FractionRing (MvPolynomial (Fin r) ℚ)
  let : Algebra ℚ K := inferInstanceAs (Algebra ℚ (FractionRing (MvPolynomial (Fin r) ℚ)))
  have intDomainTower := IsScalarTower.of_algebraMap_eq' (R := ℤ) (S := D) (A := K)
    (Subsingleton.elim _ _)
  have intRatTower := IsScalarTower.of_algebraMap_eq' (R := ℤ) (S := ℚ) (A := K)
    (Subsingleton.elim _ _)
  have : CharZero K := Algebra.charZero_of_charZero ℚ K
  have : CharZero D :=
    ⟨fun _ _ h ↦ Nat.cast_injective (R := K) (by simpa using congrArg D.subtype h)⟩
  let : Algebra.IsAlgebraic D K := IsLocalization.isAlgebraic K D⁰
  have hD : trdeg ℤ D = trdeg ℤ K := by
    simpa [trdeg_eq_zero (R := D) (A := K)] using trdeg_add_eq ℤ D (A := K)
  have hQ : trdeg ℤ K = trdeg ℚ K := by
    have : Algebra.IsAlgebraic ℤ ℚ := IsLocalization.isAlgebraic ℚ ℤ⁰
    simpa [trdeg_eq_zero (R := ℤ) (A := ℚ)] using (trdeg_add_eq ℤ ℚ (A := K)).symm
  exact hD.trans (hQ.trans (rationalFunctionField_trdeg r))

end UnconditionalCounterexample.Variations
