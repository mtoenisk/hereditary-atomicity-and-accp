import HereditaryAtomicity.ArithmeticProfiles
import Mathlib.FieldTheory.Minpoly.Finite
import Mathlib.Data.Nat.Factorial.Basic

/-!
# One lattice for all profile values in a finite field level

For a normalized family of valuations above a DVR, the factorial of the finite field
degree clears the denominators of all values at that level. The bound depends on the
level.
-/

noncomputable section
namespace HereditaryAtomicity
open scoped NNReal

theorem polynomial_order_factorial_integral
    {k L : Type*} [Field k] [Field L] (f : k →+* L)
    (v : Valuation L ℝ≥0) (p : Polynomial k) (hp : p ≠ 0)
    (hcoeff : ∀ a : k, a ≠ 0 → ∃ z : ℤ, realValuationOrder v (f a) = z)
    (d : ℕ) (hdeg : p.natDegree ≤ d)
    {x : L} (hx : x ≠ 0) (hpx : p.eval₂ f x = 0) :
    ∃ z : ℤ, (d.factorial : ℝ) * realValuationOrder v x = z := by
  obtain ⟨i, hi, j, hj, hij, heq, _⟩ :=
    polynomial_exists_maximal_valuation_tie f f.injective v p hp x hx hpx
  obtain ⟨a, ha⟩ := hcoeff (p.coeff i) (Polynomial.mem_support_iff.mp hi)
  obtain ⟨b, hb⟩ := hcoeff (p.coeff j) (Polynomial.mem_support_iff.mp hj)
  have hci : f (p.coeff i) ≠ 0 := (map_ne_zero_iff f f.injective).mpr (Polynomial.mem_support_iff.mp hi)
  have hcj : f (p.coeff j) ≠ 0 := (map_ne_zero_iff f f.injective).mpr (Polynomial.mem_support_iff.mp hj)
  have ho := congrArg (fun z : ℝ≥0 => -Real.log (z : ℝ)) heq
  change realValuationOrder v (f (p.coeff i) * x ^ i) =
    realValuationOrder v (f (p.coeff j) * x ^ j) at ho
  rw [realValuationOrder_mul _ hci (pow_ne_zero _ hx),
    realValuationOrder_mul _ hcj (pow_ne_zero _ hx),
    realValuationOrder_pow, realValuationOrder_pow, ha, hb] at ho
  have hji : j - i ≤ d := (Nat.sub_le j i).trans
    ((Polynomial.le_natDegree_of_mem_supp j hj).trans hdeg)
  obtain ⟨m, hm⟩ := Nat.dvd_factorial (Nat.sub_pos_of_lt hij) hji
  refine ⟨(a - b) * m, ?_⟩
  have hcast : (j : ℝ) - i = (j - i : ℕ) := by
    rw [Nat.cast_sub hij.le]
  have hm' : (d.factorial : ℝ) = (j - i : ℕ) * (m : ℝ) := by exact_mod_cast hm
  push_cast
  rw [hm']
  have hbase : (j - i : ℕ) * realValuationOrder v x = (a : ℝ) - b := by
    rw [← hcast]
    nlinarith only [ho]
  calc
    _ = ((j - i : ℕ) * realValuationOrder v x) * (m : ℝ) := by ring
    _ = _ := by rw [hbase]

theorem normalized_dvr_fraction_orders
    (A k L : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field k] [Field L] [Algebra A k] [IsFractionRing A k]
    (f : k →+* L) {ι : Type*} (v : ι → Valuation L ℝ≥0)
    (hv : ∀ i a, v i (f (algebraMap A k a)) ≤ 1)
    {π : A} (hπ : Irreducible π)
    (hnorm : ∀ i, realValuationOrder (v i) (f (algebraMap A k π)) = 1)
    {x : k} (hx : x ≠ 0) :
    ∃ z : ℤ, ∀ i, realValuationOrder (v i) (f x) = z := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective A x
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have ha0 : a ≠ 0 := by contrapose! hx; simp [hx]
  obtain ⟨n, hn⟩ := normalized_dvr_coefficient_orders
    (f.comp (algebraMap A k)) v hv hπ hnorm ha0
  obtain ⟨m, hm⟩ := normalized_dvr_coefficient_orders
    (f.comp (algebraMap A k)) v hv hπ hnorm hb0
  refine ⟨(n : ℤ) - m, fun i => ?_⟩
  have haL : f (algebraMap A k a) ≠ 0 :=
    (map_ne_zero_iff f f.injective).mpr ((map_ne_zero_iff _ (IsFractionRing.injective A k)).mpr ha0)
  have hbL : f (algebraMap A k b) ≠ 0 :=
    (map_ne_zero_iff f f.injective).mpr ((map_ne_zero_iff _ (IsFractionRing.injective A k)).mpr hb0)
  rw [map_div₀, realValuationOrder_div _ haL hbL]
  simpa only [RingHom.comp_apply, Int.cast_sub, Int.cast_natCast] using congrArg₂ (· - ·) (hn i) (hm i)

theorem finiteExtension_order_factorial_integral
    (A k L : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field k] [Field L] [Algebra A k] [IsFractionRing A k]
    [Algebra k L] [FiniteDimensional k L]
    {ι : Type*} (v : ι → Valuation L ℝ≥0)
    (hv : ∀ i a, v i (algebraMap k L (algebraMap A k a)) ≤ 1)
    {π : A} (hπ : Irreducible π)
    (hnorm : ∀ i, realValuationOrder (v i)
      (algebraMap k L (algebraMap A k π)) = 1)
    {x : L} (hx : x ≠ 0) (i : ι) :
    ∃ z : ℤ, ((Module.finrank k L).factorial : ℝ) * realValuationOrder (v i) x = z := by
  refine polynomial_order_factorial_integral (algebraMap k L) (v i) (minpoly k x)
    (minpoly.ne_zero (Algebra.IsIntegral.isIntegral x))
    (fun a ha => ?_) _ (minpoly.natDegree_le x) hx (minpoly.aeval k x)
  obtain ⟨z, hz⟩ := normalized_dvr_fraction_orders A k L (algebraMap k L) v hv hπ hnorm ha
  exact ⟨z, hz i⟩

/-- A single positive denominator works for every nonzero element in the finite
extension, independently of the number of containing valuation branches. -/
theorem exists_common_finiteExtension_order_lattice
    (A k L : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field k] [Field L] [Algebra A k] [IsFractionRing A k]
    [Algebra k L] [FiniteDimensional k L]
    {ι : Type*} (v : ι → Valuation L ℝ≥0)
    (hv : ∀ i a, v i (algebraMap k L (algebraMap A k a)) ≤ 1)
    {π : A} (hπ : Irreducible π)
    (hnorm : ∀ i, realValuationOrder (v i)
      (algebraMap k L (algebraMap A k π)) = 1) :
    ∃ e : ℕ, 0 < e ∧ ∀ x : L, x ≠ 0 → ∀ i, ∃ z : ℤ,
      realValuationOrder (v i) x = (z : ℝ) / e := by
  refine ⟨(Module.finrank k L).factorial, Nat.factorial_pos _, fun x hx i => ?_⟩
  obtain ⟨z, hz⟩ := finiteExtension_order_factorial_integral A k L v hv hπ hnorm hx i
  refine ⟨z, (eq_div_iff (by exact_mod_cast (Nat.factorial_pos (Module.finrank k L)).ne')).mpr ?_⟩
  simpa only [mul_comm] using hz

end HereditaryAtomicity
