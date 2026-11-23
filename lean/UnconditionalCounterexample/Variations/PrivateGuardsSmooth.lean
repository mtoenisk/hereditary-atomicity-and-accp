import Mathlib.RingTheory.Nullstellensatz
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Algebra.BigOperators.Associated
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Smooth algebraic points for the private evaluations

On an irreducible rational hypersurface one can find an algebraic point off all
finitely many test hypersurfaces with a nonvanishing partial derivative.
The prime ideal and Nullstellensatz argument works over the original coefficient
field even when the defining polynomial is not absolutely irreducible.
-/

noncomputable section
namespace UnconditionalCounterexample.Variations.PrivateGuards

open MvPolynomial

private theorem exists_partial {k σ : Type*} [Field k] [CharZero k]
    (G : MvPolynomial σ k) (hg : Irreducible G) : ∃ i, ¬ G ∣ pderiv i G := by
  classical
  have hvars : G.vars.Nonempty := by
    by_contra! hempty
    have hc := (vars_eq_empty_iff_eq_C (p := G)).mp hempty
    have hne : G.coeff 0 ≠ 0 := by
      intro hz
      exact hg.ne_zero (by simpa [hz] using hc)
    exact hg.not_isUnit (hc ▸ (isUnit_iff_ne_zero.mpr hne).map C)
  obtain ⟨i,hi⟩ := hvars
  obtain ⟨s, hs, hsi⟩ := (mem_vars_iff_mem_support i).mp hi
  let u := s - Finsupp.single i 1
  have he : u + Finsupp.single i 1 = s :=
    Finsupp.sub_add_single_one_cancel (Finsupp.mem_support_iff.mp hsi)
  have hpartial : pderiv i G ≠ 0 := by
    intro hz
    have hzero := congrArg (fun f : MvPolynomial σ k => f.coeff u) hz
    change (pderiv i G).coeff u = 0 at hzero
    rw [coeff_pderiv, he] at hzero
    exact (mul_ne_zero (mem_support_iff.mp hs) (by exact_mod_cast Nat.succ_ne_zero (u i))) hzero
  have hdeg : (pderiv i G).degreeOf i < G.degreeOf i := by
    apply (degreeOf_lt_iff (Nat.pos_of_ne_zero (mem_vars_iff_degreeOf_ne_zero.mp hi))).mpr
    intro m hm
    have hc := mem_support_iff.mp hm
    rw [coeff_pderiv] at hc
    have hle := monomial_le_degreeOf i (mem_support_iff.mpr (left_ne_zero_of_mul hc))
    simpa only [Finsupp.add_apply, Finsupp.single_eq_same, Nat.add_one_le_iff] using hle
  refine ⟨i, ?_⟩
  rintro ⟨H, heq⟩
  have hH : H ≠ 0 := by
    rintro rfl
    simp_all
  rw [heq, degreeOf_mul_eq hg.ne_zero hH] at hdeg
  omega

/-- An algebraic smooth point on a prescribed irreducible hypersurface,
simultaneously off a finite set of tests. -/
theorem exists_smooth_point {k σ : Type*} [Field k] [CharZero k] [Finite σ]
    (G : MvPolynomial σ k) (hg : Irreducible G) (tests : Finset (MvPolynomial σ k))
    (ht : ∀ f ∈ tests, ¬ G ∣ f) :
    ∃ (i : σ) (x : σ → AlgebraicClosure k), aeval x G = 0 ∧ aeval x (pderiv i G) ≠ 0 ∧
      ∀ f ∈ tests, aeval x f ≠ 0 := by
  classical
  obtain ⟨i, hder⟩ := exists_partial G hg
  let J := Ideal.span ({G} : Set (MvPolynomial σ k))
  let : J.IsPrime := Ideal.isPrime_span_singleton_of_prime hg.prime
  let H := pderiv i G * ∏ f ∈ tests, f
  have hH : H ∉ J := by
    intro h
    rcases hg.prime.dvd_or_dvd (Ideal.mem_span_singleton.mp h) with hd | hp
    · exact hder hd
    · obtain ⟨f,hft,hgf⟩ := hg.prime.exists_mem_finset_dvd hp
      exact ht f hft hgf
  have hV : H ∉ vanishingIdeal k (zeroLocus (AlgebraicClosure k) J) := by
    rwa [MvPolynomial.IsPrime.vanishingIdeal_zeroLocus]
  rw [mem_vanishingIdeal_iff] at hV
  push Not at hV
  obtain ⟨x,hx,hHx⟩ := hV
  have hprod : aeval x (pderiv i G) * (∏ f ∈ tests, aeval x f) ≠ 0 := by simpa [H] using hHx
  exact ⟨i, x, hx G (Ideal.subset_span (Set.mem_singleton _)), left_ne_zero_of_mul hprod,
    fun f hf => (Finset.prod_ne_zero_iff.mp (right_ne_zero_of_mul hprod)) f hf⟩

end UnconditionalCounterexample.Variations.PrivateGuards
