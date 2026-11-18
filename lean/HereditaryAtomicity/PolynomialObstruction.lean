import Factorization.Hereditary
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.Basic

/-!
# A nonatomic polynomial coefficient subring

For a coefficient subring A of a domain B, the polynomials over B whose constant
coefficient lies in A form A + X B[X]. If a nonunit of A becomes a unit of B,
no irreducible of this subring can have zero constant coefficient, whereas X
does. This gives the explicit nonatomic subring in CGH Theorem 6.4(1).
-/

noncomputable section

namespace HereditaryAtomicity

open Polynomial Factorization

universe u
variable {B : Type u} [CommRing B] [IsDomain B]

/-- Polynomials with constant coefficient in the specified coefficient subring. -/
def constantCoefficientSubring (A : Subring B) : Subring B[X] :=
  A.comap Polynomial.constantCoeff

/-- Constant coefficient as a map to the smaller coefficient ring. -/
def coefficientMap (A : Subring B) : constantCoefficientSubring A →+* A where
  toFun p := ⟨p.val.coeff 0, p.property⟩
  map_zero' := Subtype.ext (by simp)
  map_one' := Subtype.ext (by simp)
  map_add' p q := Subtype.ext (by simp)
  map_mul' p q := Subtype.ext (by simp [mul_coeff_zero])

/-- A polynomial with zero constant coefficient is a nonunit in the coefficient
subring, since its image under constant coefficient is zero. -/
theorem not_isUnit_of_constantCoeff_eq_zero (A : Subring B)
    (p : constantCoefficientSubring A) (hp : p.val.coeff 0 = 0) : ¬ IsUnit p := by
  intro hu
  have hmap := hu.map (coefficientMap A)
  have hzero : coefficientMap A p = 0 := Subtype.ext hp
  rw [hzero] at hmap
  exact not_isUnit_zero hmap

/-- A nonunit coefficient becoming invertible in B prevents every nonzero
zero-constant polynomial from being irreducible in A + X B[X]. -/
theorem not_irreducible_of_constantCoeff_eq_zero (A : Subring B) (b : A)
    (hb : ¬ IsUnit b) (hB : IsUnit (b : B))
    (p : constantCoefficientSubring A) (hp : p.val.coeff 0 = 0) : ¬ Irreducible p := by
  obtain ⟨u, hu⟩ := hB
  let a : constantCoefficientSubring A := ⟨C (b : B), by
    change (C (b : B)).coeff 0 ∈ A
    simp only [coeff_C_zero]
    exact b.property⟩
  let q : constantCoefficientSubring A := ⟨C ((u⁻¹ : Bˣ) : B) * p.val, by
    change (C ((u⁻¹ : Bˣ) : B) * p.val).coeff 0 ∈ A
    simp [mul_coeff_zero, hp]⟩
  have ha : ¬ IsUnit a := by
    intro ha
    apply hb
    have hmap := ha.map (coefficientMap A)
    simpa [coefficientMap, a] using hmap
  have hq : ¬ IsUnit q := by
    apply not_isUnit_of_constantCoeff_eq_zero A q
    simp [q, mul_coeff_zero, hp]
  have hprod : p = a * q := by
    apply Subtype.ext
    change p.val = C (b : B) * (C ((u⁻¹ : Bˣ) : B) * p.val)
    rw [← mul_assoc, ← map_mul, ← hu]
    simp
  intro hirr
  exact (hirr.isUnit_or_isUnit hprod).elim ha hq

/-- A coefficient nonunit invertible in B produces an actual nonatomic domain. -/
theorem not_isAtomicDomain_constantCoefficientSubring (A : Subring B) (b : A)
    (hb : ¬ IsUnit b) (hB : IsUnit (b : B)) :
    ¬ IsAtomicDomain (constantCoefficientSubring A) := by
  intro hAtomic
  let x : constantCoefficientSubring A := ⟨X, by
    change (X : B[X]).coeff 0 ∈ A
    simp⟩
  have hx : x ≠ 0 := by
    intro hx
    have : (X : B[X]) = 0 := congrArg Subtype.val hx
    exact X_ne_zero this
  obtain ⟨factors, hirr, hprod⟩ := hAtomic x hx
  have hcoeff : ∀ a ∈ factors, coefficientMap A a ≠ 0 := by
    intro a ha hzero
    apply not_irreducible_of_constantCoeff_eq_zero A b hb hB a
      (congrArg Subtype.val hzero)
    exact hirr a ha
  have hne : (factors.map (coefficientMap A)).prod ≠ 0 := by
    apply Multiset.prod_ne_zero
    intro hzero
    obtain ⟨a, ha, heq⟩ := Multiset.mem_map.mp hzero
    exact hcoeff a ha heq
  have hassoc := hprod.map (coefficientMap A).toMonoidHom
  change Associated (coefficientMap A factors.prod) (coefficientMap A x) at hassoc
  have hzero : coefficientMap A x = 0 := Subtype.ext (by simp [x, coefficientMap])
  rw [hzero] at hassoc
  apply hne
  rw [← map_multiset_prod]
  exact hassoc.eq_zero_iff.mpr rfl

end HereditaryAtomicity
