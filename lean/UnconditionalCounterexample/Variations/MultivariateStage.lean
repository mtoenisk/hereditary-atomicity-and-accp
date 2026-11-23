import UnconditionalCounterexample.Variations.MultivariateFibres
import UnconditionalCounterexample.PolynomialAvoidance

/-!
# Finite geometry tests for the multivariate selector

Constant and linear perturbations suffice to impose all the finite point,
separation and directional derivative tests on the listed multivariate
words. The coefficient choices can be made on any arithmetic grid.
-/

namespace UnconditionalCounterexample.MultivariateStage

open MvPolynomial MultivariateFibres

variable {k σ : Type*} [Field k] [Fintype σ]

noncomputable def directional (u v : σ → k) (p : MvPolynomial σ k) : k :=
  ∑ i, gradient u p i * v i

/-- Add an affine-linear lower-degree perturbation with independent coefficients. -/
noncomputable def perturb (p : MvPolynomial σ k) (z : Option σ → k) : MvPolynomial σ k :=
  p + C (z none) + ∑ i : σ, C (z (some i)) * X i

private noncomputable def valueForm (p : MvPolynomial σ k) (u : σ → k) : MvPolynomial (Option σ) k :=
  C (eval u p) + X none + ∑ i, X (some i) * C (u i)

private noncomputable def directionForm (p : MvPolynomial σ k) (u v : σ → k) :
    MvPolynomial (Option σ) k :=
  C (directional u v p) + ∑ i, X (some i) * C (v i)

private theorem valueForm_eval (p : MvPolynomial σ k) (u : σ → k) (z : Option σ → k) :
    eval z (valueForm p u) = eval u (perturb p z) := by simp [valueForm, perturb]

private theorem gradient_perturb (p : MvPolynomial σ k) (u : σ → k) (z : Option σ → k) (i : σ) :
    gradient u (perturb p z) i = gradient u p i + z (some i) := by
  classical
  simp [perturb, gradient, Pi.single_apply, mul_ite]

private theorem directionForm_eval (p : MvPolynomial σ k) (u v : σ → k) (z : Option σ → k) :
    eval z (directionForm p u v) = directional u v (perturb p z) := by
  simp [directionForm, directional, gradient_perturb, add_mul, Finset.sum_add_distrib]

/-- Each word has numerator `F^a` and a fixed denominator `H`. -/
inductive Test (k σ : Type*) [Field k]
  | point (u : σ → k)
  | pair (u w : σ → k) (a : ℕ) (H : MvPolynomial σ k)
  | tangent (u v : σ → k) (a : ℕ) (H : MvPolynomial σ k)

def Test.Valid : Test k σ → Prop
  | .point _ => True
  | .pair u w a H => u ≠ w ∧ 0 < a ∧ eval u H ≠ 0 ∧ eval w H ≠ 0
  | .tangent u v a H => v ≠ 0 ∧ 0 < a ∧ eval u H ≠ 0

/-- The geometric tests use the actual word value and quotient-rule derivative. -/
def Test.Holds (p : MvPolynomial σ k) : Test k σ → Prop
  | .point u => eval u p ≠ 0
  | .pair u w a H => eval u p ^ a * eval w H ≠ eval w p ^ a * eval u H
  | .tangent u v a H => quotientDerivativeNumerator u v (p ^ a) H ≠ 0

private noncomputable def Test.polynomial (p : MvPolynomial σ k) : Test k σ → MvPolynomial (Option σ) k
  | .point u => valueForm p u
  | .pair u w a H => valueForm p u ^ a * C (eval w H) - valueForm p w ^ a * C (eval u H)
  | .tangent u v a H => C (a : k) * valueForm p u ^ (a-1) * directionForm p u v * C (eval u H)
      - valueForm p u ^ a * C (directional u v H)

private theorem directional_pow (p : MvPolynomial σ k) (u v : σ → k) (a : ℕ) :
    directional u v (p ^ a) = (a : k) * eval u p ^ (a - 1) * directional u v p := by
  simp only [directional, gradient, pderiv_pow, map_mul, map_natCast, map_pow, Finset.mul_sum, mul_assoc]

private theorem Test.holds_iff (t : Test k σ) (p : MvPolynomial σ k) (z : Option σ → k) :
    t.Holds (perturb p z) ↔ eval z (t.polynomial p) ≠ 0 := by
  have hd (u v : σ → k) (f H : MvPolynomial σ k) :
      quotientDerivativeNumerator u v f H = directional u v f * eval u H -
        eval u f * directional u v H := rfl
  cases t <;> simp [Test.Holds, Test.polynomial, valueForm_eval, directionForm_eval,
    hd, directional_pow, sub_ne_zero]

private theorem exists_pair_params (p : MvPolynomial σ k) {u w : σ → k} (hne : u ≠ w) :
    ∃ z : Option σ → k, eval z (valueForm p u) = 0 ∧ eval z (valueForm p w) = 1 := by
  classical
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hne
  let b := (1 - eval w p + eval u p) / (w i - u i)
  let z : Option σ → k := Option.elim' (-eval u p - b * u i) (Pi.single i b)
  have hv (a : σ → k) : eval z (valueForm p a) = eval a p - eval u p - b * u i + b * a i := by
    simp [valueForm, z, Pi.single_apply, ite_mul]; ring
  refine ⟨z, ?_, ?_⟩
  · rw [hv]; ring
  · rw [hv]; dsimp [b]; field_simp [sub_ne_zero.mpr hi.symm]; ring

private theorem exists_tangent_params (p : MvPolynomial σ k) {u v : σ → k} (hv : v ≠ 0)
    (t : k) : ∃ z : Option σ → k,
      eval z (valueForm p u) = 1 ∧ eval z (directionForm p u v) = t := by
  classical
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hv
  change v i ≠ 0 at hi
  let b := (t - directional u v p) / v i
  let z : Option σ → k := Option.elim' (1 - eval u p - b * u i) (Pi.single i b)
  refine ⟨z, ?_, ?_⟩
  · simp [valueForm, z, Pi.single_apply, ite_mul]; ring
  · simp [directionForm, z, Pi.single_apply, ite_mul, b, hi]

private theorem Test.polynomial_ne_zero [CharZero k] (p : MvPolynomial σ k) (t : Test k σ)
    (ht : t.Valid) : t.polynomial p ≠ 0 := by
  intro heq
  cases t with
  | point u =>
    let z : Option σ → k := Option.elim' (1 - eval u p) (fun _ => 0)
    have h := congrArg (eval z) heq
    simp [Test.polynomial, valueForm, z] at h
  | pair u w a H =>
    obtain ⟨hne, ha, hH, _⟩ := ht
    obtain ⟨z, hu, hw⟩ := exists_pair_params p hne
    have h := congrArg (eval z) heq
    simp [Test.polynomial, hu, hw, Nat.ne_of_gt ha, hH] at h
  | tangent u v a H =>
    obtain ⟨hv, ha, hH⟩ := ht
    let c := (a : k) * eval u H
    have hc : c ≠ 0 := mul_ne_zero (Nat.cast_ne_zero.mpr ha.ne') hH
    obtain ⟨z, hu, hd⟩ := exists_tangent_params (u := u) p hv ((directional u v H + 1) / c)
    have h := congrArg (eval z) heq
    simp only [Test.polynomial, map_sub, map_mul, map_pow, eval_C, hu, one_pow, mul_one, hd,
      one_mul, map_zero, sub_eq_zero] at h
    have hh : c * ((directional u v H + 1) / c) = directional u v H := by
      dsimp [c]; linear_combination h
    rw [mul_div_cancel₀ _ hc] at hh
    exact one_ne_zero (by linear_combination hh)

/-- All simultaneous finite geometric exclusions are met by a rational choice
of the affine perturbation on the specified arithmetic grid. -/
theorem exists_grid_perturbation [CharZero k] (p : MvPolynomial σ k) (T : Finset (Test k σ))
    (hT : ∀ t ∈ T, t.Valid) (b m : Option σ → ℚ) (hm : ∀ i, m i ≠ 0) (N : Option σ → ℕ) :
    ∃ n : Option σ → ℕ, ∀ t ∈ T,
      t.Holds (perturb p (fun i => algebraMap ℚ k (b i + m i * ((N i + n i : ℕ) : ℚ)))) := by
  obtain ⟨n, hn⟩ := PolynomialAvoidance.exists_rational_grid_avoiding b m hm N T
    (fun t => t.polynomial p) (fun t ht => t.polynomial_ne_zero p (hT t ht))
  exact ⟨n, fun t ht => (t.holds_iff _ _).mpr (hn t ht)⟩

/-- The selected coefficients are rational, and perturbing below degree two
preserves a prescribed leading power of degree at least two. -/
theorem exists_rational_perturbation [CharZero k] (l p : MvPolynomial σ ℚ)
    (d : ℕ) (hd : 2 ≤ d) (hp : p.totalDegree < d) (T : Finset (Test k σ))
    (hT : ∀ t ∈ T, t.Valid) (b m : Option σ → ℚ) (hm : ∀ i, m i ≠ 0) (N : Option σ → ℕ) :
    ∃ n : Option σ → ℕ, ∃ q : MvPolynomial σ ℚ, q.totalDegree < d ∧
      q = perturb p (fun i => b i + m i * ((N i + n i : ℕ) : ℚ)) ∧
      ∀ t ∈ T, t.Holds (MvPolynomial.map (algebraMap ℚ k) (l ^ d + q)) := by
  obtain ⟨n,hn⟩ := exists_grid_perturbation (MvPolynomial.map (algebraMap ℚ k) (l ^ d + p))
    T hT b m hm N
  let z (i : Option σ) : ℚ := b i + m i * ((N i + n i : ℕ) : ℚ)
  refine ⟨n,perturb p z,?_,rfl,?_⟩
  · apply (totalDegree_add _ _).trans_lt (max_lt ?_ ?_)
    · apply (totalDegree_add _ _).trans_lt (max_lt hp ?_)
      simp; omega
    · apply lt_of_le_of_lt (b := 1) (totalDegree_finsetSum_le (fun i _ => ?_)) (by omega)
      exact (totalDegree_mul _ _).trans (by simp)
  · intro t ht
    have heq : MvPolynomial.map (algebraMap ℚ k) (l ^ d + perturb p z) =
        perturb (MvPolynomial.map (algebraMap ℚ k) (l ^ d + p)) (fun i => algebraMap ℚ k (z i)) := by
      simp [perturb, add_assoc]
    rw [heq]; exact hn t ht

end UnconditionalCounterexample.MultivariateStage
