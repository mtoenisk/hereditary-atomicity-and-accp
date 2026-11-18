import HereditaryAtomicity.PolynomialObstruction
import Mathlib.RingTheory.Localization.Integral
import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.Algebra.Field.Subfield.Basic

/-!
# Unit and transcendence obstruction to hereditary atomicity

CGH Theorem 6.4(1): a nonintegral unit and an independent transcendental element
produce an actual nonatomic subring. The polynomial coefficient obstruction is
proved separately; the reciprocal-polynomial step uses mathlib's integral
adjoin theorem. No field-classification result is assumed.
-/

noncomputable section

namespace HereditaryAtomicity

open Polynomial Factorization

universe u v

/-- The inverse of a nonintegral unit is a nonunit in the subring it generates
over the integers (equivalently, over the prime subring). -/
theorem inverse_not_isUnit_adjoin_int {B : Type u} [CommRing B]
    (u : Bˣ) (hu : ¬ IsIntegral ℤ (u : B)) :
    ¬ IsUnit (⟨((u⁻¹ : Bˣ) : B), Algebra.subset_adjoin (Set.mem_singleton _)⟩ :
      Algebra.adjoin ℤ ({((u⁻¹ : Bˣ) : B)} : Set B)) := by
  let A := Algebra.adjoin ℤ ({((u⁻¹ : Bˣ) : B)} : Set B)
  intro hs
  obtain ⟨w, hw⟩ := hs.exists_right_inv
  have hwB : ((u⁻¹ : Bˣ) : B) * (w : B) = 1 := congrArg Subtype.val hw
  have hwu : (w : B) = (u : B) := by
    calc
      (w : B) = (u : B) * (((u⁻¹ : Bˣ) : B) * (w : B)) := by simp
      _ = (u : B) := by rw [hwB, mul_one]
  have huA : (u : B) ∈ A := hwu ▸ w.property
  have hint : IsIntegral A (u : B) :=
    isIntegral_algebraMap (x := (⟨u, huA⟩ : A))
  exact hu (isIntegral_of_isIntegral_adjoin_of_mul_eq_one (R := ℤ)
    (u : B) ((u⁻¹ : Bˣ) : B) (by simp) hint)

/-- A coefficient unit nonintegral over the integers forces algebraicity of
every ambient element in a hereditarily atomic domain. -/
theorem isAlgebraic_of_nonintegral_coefficient_unit
    {R : Type u} [CommRing R] [IsDomain R]
    (hR : IsHereditarilyAtomic R) (B : Subring R) (u : Bˣ)
    (hu : ¬ IsIntegral ℤ (u : B)) (x : R) : IsAlgebraic B x := by
  by_contra hx
  have heval : Function.Injective (aeval x : B[X] →ₐ[B] R) :=
    transcendental_iff_injective.mp hx
  have hPolynomial : IsHereditarilyAtomic B[X] :=
    hR.of_injective (aeval x).toRingHom heval
  let A := Algebra.adjoin ℤ ({((u⁻¹ : Bˣ) : B)} : Set B)
  let b : A.toSubring := ⟨((u⁻¹ : Bˣ) : B), Algebra.subset_adjoin (Set.mem_singleton _)⟩
  have hb : ¬ IsUnit b := inverse_not_isUnit_adjoin_int u hu
  exact not_isAtomicDomain_constantCoefficientSubring A.toSubring b hb u⁻¹.isUnit
    (hPolynomial (constantCoefficientSubring A.toSubring))

/-- Coefficients in an ambient subfield, pulled back to a possibly smaller domain. -/
def subfieldCoefficientSubring {R : Type u} {K : Type v}
    [CommRing R] [Field K] (f : R →+* K) (F : Subfield K) : Subring R :=
  F.toSubring.comap f

/-- The pulled-back coefficient ring maps canonically into the chosen field. -/
def subfieldCoefficientMap {R : Type u} {K : Type v}
    [CommRing R] [Field K] (f : R →+* K) (F : Subfield K) :
    subfieldCoefficientSubring f F →+* F where
  toFun a := ⟨f a.val, a.property⟩
  map_zero' := Subtype.ext f.map_zero
  map_one' := Subtype.ext f.map_one
  map_add' a b := Subtype.ext (f.map_add a b)
  map_mul' a b := Subtype.ext (f.map_mul a b)

/-- CGH's obstruction in a field containing the domain: once a subfield contains
a nonintegral ambient unit, every domain element is algebraic over that field. -/
theorem isAlgebraic_over_subfield_of_nonintegral_unit
    {R : Type u} {K : Type v} [CommRing R] [IsDomain R] [Field K]
    (hR : IsHereditarilyAtomic R) (f : R →+* K) (hf : Function.Injective f)
    (u : Rˣ) (hu : ¬ IsIntegral ℤ (u : R)) (F : Subfield K)
    (huF : f (u : R) ∈ F) (x : R) : IsAlgebraic F (f x) := by
  let B := subfieldCoefficientSubring f F
  have huinvF : f ((u⁻¹ : Rˣ) : R) ∈ F := by
    rw [map_units_inv]
    exact F.inv_mem huF
  let uB : Bˣ := {
    val := ⟨u, huF⟩
    inv := ⟨(u⁻¹ : Rˣ), huinvF⟩
    val_inv := Subtype.ext (by simp)
    inv_val := Subtype.ext (by simp) }
  have huB : ¬ IsIntegral ℤ (uB : B) := by
    intro hint
    exact hu (map_isIntegral_int B.subtype hint)
  have hx := isAlgebraic_of_nonintegral_coefficient_unit hR B uB huB x
  apply hx.ringHom_of_comp_eq (subfieldCoefficientMap f F) f
  · intro a b hab
    apply Subtype.ext
    apply hf
    exact congrArg Subtype.val hab
  · ext a
    rfl

end HereditaryAtomicity
