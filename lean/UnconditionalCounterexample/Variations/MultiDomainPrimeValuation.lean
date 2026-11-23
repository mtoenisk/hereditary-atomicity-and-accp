import Mathlib.RingTheory.Valuation.ExtendToLocalization
import Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicity
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Algebra.Order.GroupWithZero.WithZero

/-!
# Prime orders in the fraction field of a factorial domain

The order at a prime polynomial extends to the multivariate fraction field
with value group the multiplicative integers. Its value on a nonzero
polynomial records the ordinary multiplicity.
-/

noncomputable section
namespace UnconditionalCounterexample.Variations.MultiDomain.PrimeOrders

open WithZero
open scoped nonZeroDivisors

variable {R : Type*} [CommRing R] [IsDomain R] [WfDvdMonoid R] {p : R} (hp : Prime p)

private def value (x : R) : ℤᵐ⁰ := by
  classical exact if x = 0 then 0 else exp (-(multiplicity p x : ℤ))

include hp

private theorem value_add (x y : R) : value (p := p) (x+y) ≤ max (value (p := p) x) (value (p := p) y) := by
  classical
  by_cases hx : x = 0
  · simp [hx, value]
  by_cases hy : y = 0
  · simp [hy, value]
  by_cases hxy : x+y = 0
  · simp [hxy, value]
  simp only [value, ite_eq_right hx, ite_eq_right hy, ite_eq_right hxy]
  let n := min (multiplicity p x) (multiplicity p y)
  have ha : p^n ∣ x := (FiniteMultiplicity.of_prime_left hp hx).pow_dvd_iff_le_multiplicity.mpr (min_le_left ..)
  have hb : p^n ∣ y := (FiniteMultiplicity.of_prime_left hp hy).pow_dvd_iff_le_multiplicity.mpr (min_le_right ..)
  have hn := (FiniteMultiplicity.of_prime_left hp hxy).le_multiplicity_of_pow_dvd (dvd_add ha hb)
  rcases le_total (multiplicity p x) (multiplicity p y) with h | h
  · apply le_trans _ (le_max_left _ _)
    apply exp_le_exp.mpr
    simpa [n, min_eq_left h] using (show -(multiplicity p (x+y) : ℤ) ≤ -(n : ℤ) by exact_mod_cast neg_le_neg (Int.ofNat_le.mpr hn))
  · apply le_trans _ (le_max_right _ _)
    apply exp_le_exp.mpr
    simpa [n, min_eq_right h] using (show -(multiplicity p (x+y) : ℤ) ≤ -(n : ℤ) by exact_mod_cast neg_le_neg (Int.ofNat_le.mpr hn))

def polynomialValuation : Valuation R ℤᵐ⁰ where
  toFun := value (p := p)
  map_zero' := by simp [value]
  map_one' := by simp [value]
  map_mul' x y := by
    classical
    by_cases hx : x = 0
    · simp [hx, value]
    by_cases hy : y = 0
    · simp [hy, value]
    simp [value, hx, hy, multiplicity_mul hp (FiniteMultiplicity.of_prime_left hp (mul_ne_zero hx hy)),
      exp_add, mul_comm]
  map_add_le_max' := value_add hp

private theorem regular : R⁰ ≤ (polynomialValuation hp).supp.primeCompl := by
  intro x hx
  change value (p := p) x ≠ 0
  simp [value, mem_nonZeroDivisors_iff_ne_zero.mp hx]

def valuation : Valuation (FractionRing R) ℤᵐ⁰ :=
  (polynomialValuation hp).extendToLocalization (regular hp) (FractionRing R)

theorem valuation_of_polynomial {f : R} (hf : f ≠ 0) :
    valuation hp (algebraMap R (FractionRing R) f) = exp (-(multiplicity p f : ℤ)) := by
  rw [valuation, Valuation.extendToLocalization_apply_map_apply]
  simp [polynomialValuation, value, hf]

theorem valuation_of_not_dvd {f : R} (h : ¬ p ∣ f) :
    valuation hp (algebraMap R (FractionRing R) f) = 1 := by
  have hf : f ≠ 0 := by rintro rfl; exact h (dvd_zero _)
  rw [valuation_of_polynomial hp hf, multiplicity_eq_zero_of_not_dvd h]
  simp

theorem valuation_self : valuation hp (algebraMap R (FractionRing R) p) = exp (-1) := by
  rw [valuation_of_polynomial hp hp.ne_zero, multiplicity_self (FiniteMultiplicity.of_prime_left hp hp.ne_zero)]
  rfl

end UnconditionalCounterexample.Variations.MultiDomain.PrimeOrders
