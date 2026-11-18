import Mathlib.RingTheory.Valuation.Basic
import Mathlib.Basic.NNReal.Basic
import Mathlib.Algebra.Polynomial.Eval.Degree

/-! A vanishing polynomial has two distinct terms of maximal valuation. -/

namespace HereditaryAtomicity
open scoped BigOperators NNReal

theorem polynomial_exists_maximal_valuation_tie
    {R K : Type*} [CommRing R] [Field K]
    (f : R →+* K) (hf : Function.Injective f) (v : Valuation K ℝ≥0)
    (p : Polynomial R) (hp : p ≠ 0) (x : K) (hx : x ≠ 0)
    (hpx : p.eval₂ f x = 0) :
    ∃ i ∈ p.support, ∃ j ∈ p.support, i < j ∧
      v (f (p.coeff i) * x^i) = v (f (p.coeff j) * x^j) ∧
      ∀ k ∈ p.support, v (f (p.coeff k) * x^k) ≤ v (f (p.coeff i) * x^i) := by
  classical
  let t : ℕ → K := fun i => f (p.coeff i) * x^i
  have hs : p.support.Nonempty := Polynomial.support_nonempty.mpr hp
  obtain ⟨i, hi, himax⟩ := p.support.exists_max_image (fun k => v (t k)) hs
  have hti : t i ≠ 0 := mul_ne_zero
    ((map_ne_zero_iff f hf).mpr (Polynomial.mem_support_iff.mp hi)) (pow_ne_zero _ hx)
  have hvi : v (t i) ≠ 0 := (Valuation.ne_zero_iff v).mpr hti
  have hsum : ∑ k ∈ p.support, t k = 0 := by
    simpa only [Polynomial.eval₂_eq_sum, Polynomial.sum, t] using hpx
  have hj : ∃ j ∈ p.support, j ≠ i ∧ v (t j) = v (t i) := by
    by_contra! h
    have hvsum := v.map_sum_eq_of_lt (f := t) hi (fun j hj => ?_)
    · rw [hsum, map_zero] at hvsum
      exact hvi hvsum.symm
    · have hj' : j ∈ p.support := (Finset.mem_sdiff.mp hj).1
      have hji : j ≠ i := by simpa using (Finset.mem_sdiff.mp hj).2
      exact lt_of_le_of_ne (himax j hj') (h j hj' hji)
  obtain ⟨j, hj, hji, heq⟩ := hj
  rcases lt_or_gt_of_ne hji with hjlt | hijlt
  · refine ⟨j, hj, i, hi, hjlt, heq, ?_⟩
    intro k hk
    exact (himax k hk).trans_eq heq.symm
  · exact ⟨i, hi, j, hj, hijlt, heq.symm, himax⟩

end HereditaryAtomicity
