import UnconditionalCounterexample.PaperPolynomialPart
import UnconditionalCounterexample.PaperPolynomialGuardBounds
import Mathlib.RingTheory.Polynomial.UniqueFactorization

/-!
# Actual divisors in the polynomial part

The monic part of a divisor belongs to the finite list of monic factors in
ℚ[t]. For each factor, the guard valuations allow only finitely many leading
coefficients of divisors in the intersection domain.
-/

noncomputable section
namespace UnconditionalCounterexample.PaperConstruction
open Polynomial

private theorem finite_of_monic_fibres {R : Type*} [CommRing R] (φ : R →+* ℚ[X])
    (hi : Function.Injective φ) (f : R) (hf : f ≠ 0)
    (hs : ∀ H : ℚ[X], H.Monic → H ∣ φ f → {q : ℚ | ∃ x : R, x ∣ f ∧ φ x = C q * H}.Finite) :
    {x : R | x ∣ f}.Finite := by
  classical
  let factors := {H : ℚ[X] // H.Monic ∧ H ∣ φ f}
  let : Fintype factors := fintypeSubtypeMonicDvd _ ((map_ne_zero_iff _ hi).mpr hf)
  let scalars (H : factors) : Set ℚ := {q | ∃ x : R, x ∣ f ∧ φ x = C q * H.val}
  have hall : (⋃ H : factors, (fun q : ℚ => C q * H.val) '' scalars H).Finite :=
    Set.finite_iUnion fun H => (hs H.val H.property.1 H.property.2).image _
  apply Set.Finite.of_finite_image (f := φ) _ hi.injOn
  apply hall.subset
  rintro _ ⟨x,hx,rfl⟩
  have hx0 : x ≠ 0 := fun he => hf (zero_dvd_iff.mp (he ▸ hx))
  have hn : φ x ≠ 0 := (map_ne_zero_iff _ hi).mpr hx0
  let a := (φ x).leadingCoeff
  let h := φ x * C a⁻¹
  have ha : a ≠ 0 := leadingCoeff_ne_zero.mpr hn
  have hmonic : h.Monic := monic_mul_leadingCoeff_inv hn
  have he : φ x = C a * h := by
    unfold h
    rw [mul_left_comm,← map_mul,mul_inv_cancel₀ ha,map_one,mul_one]
  let H : factors := ⟨h,hmonic,(show h ∣ φ x from he ▸ dvd_mul_left ..).trans (map_dvd φ hx)⟩
  exact Set.mem_iUnion.mpr ⟨H,a,⟨x,hx,he⟩,he.symm⟩

/-- Every nonzero element of the polynomial part has finitely many actual
divisors in that ring, including divisors differing by a sign. -/
theorem polynomialPart_finite_divisors (f : polynomialPart) (hf : f ≠ 0) :
    {x : polynomialPart | x ∣ f}.Finite := by
  apply finite_of_monic_fibres polynomialPartToPolynomial polynomialPartToPolynomial_injective f hf
  intro H hm _
  let ι := algebraMap ℚ[X] (RatFunc ℚ)
  have hf' : f.val.val ≠ 0 := fun he => hf (Subtype.ext (Subtype.ext he))
  apply (finite_rational_scalar_divisors f.val.val (ι H) hf' (RatFunc.algebraMap_ne_zero hm.ne_zero)).subset
  rintro q ⟨x,hx,hpoly⟩
  obtain ⟨y,hy⟩ := hx
  refine ⟨x.val,y.val,?_,congrArg (fun z : polynomialPart => z.val.val) hy.symm⟩
  rw [← polynomialPartToPolynomial_spec x,hpoly,map_mul,RatFunc.algebraMap_C]
  exact congrArg (· * ι H) (map_ratCast RatFunc.C q)

end UnconditionalCounterexample.PaperConstruction
