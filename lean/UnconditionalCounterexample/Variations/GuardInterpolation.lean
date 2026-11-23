import UnconditionalCounterexample.Variations.GuardTupleLifts
import Mathlib.RingTheory.Adjoin.Polynomial.Basic

/-!
# Integral interpolation on a guard and a rational site

If the first coordinate generates the integral guard ring and its residue
lies outside the prime field, polynomial evaluation at this coordinate and
one rational site realizes the full product of their integer rings.
-/

noncomputable section

namespace UnconditionalCounterexample.Variations.GuardUnramified

open Polynomial

private theorem paired_values {R O : Type*} [CommRing R] [CommRing O] [Algebra R O]
    {x : O} (hgen : Algebra.adjoin R ({x} : Set O) = ⊤) (y : R)
    (hunit : IsUnit (x - algebraMap R O y)) (u : O) (v : R) :
    ∃ P : R[X], aeval x P = u ∧ P.eval y = v := by
  obtain ⟨w, hw⟩ := hunit
  let a := (u - algebraMap R O v) * (w⁻¹ : Oˣ)
  have ha : a ∈ Algebra.adjoin R ({x} : Set O) := hgen ▸ Algebra.mem_top
  rw [Algebra.adjoin_singleton_eq_range_aeval] at ha
  obtain ⟨Q, hQ⟩ := ha
  refine ⟨C v + (X - C y) * Q, ?_, by simp⟩
  change aeval x Q = a at hQ
  simp only [map_add, map_mul, map_sub, aeval_X, aeval_C]
  rw [hQ]
  rw [← hw]
  change algebraMap R O v + (w : O) * ((u - algebraMap R O v) * (w⁻¹ : Oˣ)) = u
  rw [mul_left_comm, Units.mul_inv, mul_one]
  abel

variable (p : ℕ) [Fact p.Prime] (k : Type*) [Field k] [CharP k p] [Algebra (ZMod p) k]

/-- Polynomials with p-adic integral coefficients give both prescribed
integral values, even when the rational coordinate is not zero. -/
theorem guard_primary_values (x : WittVector p k)
    (hgen : Algebra.adjoin ℤ_[p] ({x} : Set (WittVector p k)) = ⊤)
    (hout : x.coeff 0 ∉ Set.range (algebraMap (ZMod p) k))
    (y : ℤ_[p]) (u : WittVector p k) (v : ℤ_[p]) :
    ∃ P : Polynomial ℤ_[p], aeval x P = u ∧ P.eval y = v := by
  apply paired_values hgen y _ u v
  apply WittVector.isUnit_of_coeff_zero_ne_zero
  change WittVector.constantCoeff (x - algebraMap ℤ_[p] (WittVector p k) y) ≠ 0
  rw [map_sub, sub_ne_zero]
  intro h
  exact hout ⟨((WittVector.equiv p).symm y).coeff 0, h.symm⟩

end UnconditionalCounterexample.Variations.GuardUnramified
