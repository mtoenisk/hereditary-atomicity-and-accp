import UnconditionalCounterexample.Variations.DimensionTensorConductor
import Mathlib.Algebra.MvPolynomial.Eval

namespace UnconditionalCounterexample.Variations

open MvPolynomial

/-- Coefficient divisibility after substituting the scaled coordinates gives literal
divisibility inside the subring containing the scaled coordinates. -/
theorem scaled_multivariate_transfer {K A σ : Type*} [Field K] [CommRing A] [Algebra K A]
    (T : Subring A) (z : σ → A) (s δ : K)
    (hz : ∀ j, algebraMap K A s * z j ∈ T) (f : MvPolynomial σ K)
    (hcoeff : ∀ m ∈ f.support, ∃ c : K, algebraMap K A c ∈ T ∧
      f.coeff m = δ * c * m.prod (fun _ n ↦ s^n)) :
    ∃ e ∈ T, aeval z f = algebraMap K A δ * e := by
  classical
  choose c hc hrep using hcoeff
  let v (m : f.support) := algebraMap K A (c m m.property) *
    m.val.prod fun j n ↦ (algebraMap K A s * z j)^n
  use ∑ m : f.support, v m
  constructor
  · apply T.sum_mem
    intro m _
    exact T.mul_mem (hc m m.property) (T.prod_mem fun j _ ↦ T.pow_mem (hz j) _)
  · conv_lhs => rw [f.as_sum, map_sum]
    rw [← Finset.sum_coe_sort, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m _
    simp [v, aeval_monomial, hrep m m.property, mul_pow, Finsupp.prod, Finset.prod_mul_distrib, mul_assoc]

/-- Normalizing a recovered word produces its required inverse uniformizer power in
the actual target. The ambient unit controls all denominator cancellations. -/
theorem scaled_word_power_mem {A : Type*} [CommRing A] (T : Subring A) (π : Aˣ)
    (hπ : (π : A) ∈ T) (F H w : A) (a t b k : ℕ) (hw : w ∈ T)
    (hH : (π : A)^b * H ∈ T) (hword : F^a = H*w) (hbound : b+k ≤ t*a) :
    (↑(π⁻¹) : A)^k * ((π : A)^t * F)^a ∈ T := by
  obtain ⟨c, hc⟩ := Nat.exists_eq_add_of_le hbound
  have hunit : (↑(π⁻¹) : A)^k * (π : A)^k = 1 := by
    rw [← mul_pow, Units.inv_mul, one_pow]
  rw [mul_pow, ← pow_mul, hc, show b+k+c = k+(c+b) by omega, pow_add, ← mul_assoc,
    ← mul_assoc, hunit, one_mul, pow_add, hword]
  simpa only [mul_assoc] using T.mul_mem (T.pow_mem hπ c) (T.mul_mem hH hw)

end UnconditionalCounterexample.Variations
