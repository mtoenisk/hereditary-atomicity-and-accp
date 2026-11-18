import UnconditionalCounterexample.CurveRecovery
import UnconditionalCounterexample.SeparationExclusions
import Mathlib.Tactic.LinearCombination
import Mathlib.FieldTheory.RatFunc.Degree

/-!
# Rational-function semantics of the geometric word tests

Cancellation identities convert F^m/H into the canonical rational-function evaluation
and first derivative. Coprimality and degree inequalities give the finite-pole and
infinity-pole tests.
-/

namespace UnconditionalCounterexample.RationalFunctionJets

open Polynomial

universe u
variable {k K : Type u} [Field k] [Field K] [Algebra k K]

/-- Any denominator nonvanishing at a point forces the reduced denominator
to be nonvanishing there as well. -/
theorem reduced_denom_ne_zero (P Q : k[X]) (α : K)
    (hQ : Q.eval₂ (algebraMap k K) α ≠ 0) :
    (algebraMap k[X] (RatFunc k) P / algebraMap k[X] (RatFunc k) Q).denom.eval₂
      (algebraMap k K) α ≠ 0 := by
  obtain ⟨r, hr⟩ := RatFunc.denom_div_dvd P Q
  rw [hr, eval₂_mul] at hQ
  exact left_ne_zero_of_mul hQ

/-- Evaluation of an arbitrary polynomial fraction at a regular point. -/
theorem eval_fraction (P Q : k[X]) (α : K)
    (hQ : Q.eval₂ (algebraMap k K) α ≠ 0) :
    RatFunc.eval (algebraMap k K) α
      (algebraMap k[X] (RatFunc k) P / algebraMap k[X] (RatFunc k) Q) =
        P.eval₂ (algebraMap k K) α / Q.eval₂ (algebraMap k K) α := by
  let x := algebraMap k[X] (RatFunc k) P / algebraMap k[X] (RatFunc k) Q
  have hQ0 : Q ≠ 0 := by intro hz; simp [hz] at hQ
  have hpoly : x.num * Q = P * x.denom := (RatFunc.num_mul_eq_mul_denom_iff hQ0).mpr rfl
  have hval := congrArg (Polynomial.eval₂ (algebraMap k K) α) hpoly
  simp only [eval₂_mul] at hval
  exact (div_eq_div_iff (reduced_denom_ne_zero P Q α hQ) hQ).mpr hval

/-- The quotient-rule expression is independent of polynomial cancellation. -/
theorem derivative_fraction (P Q : k[X]) (α : K)
    (hQ : Q.eval₂ (algebraMap k K) α ≠ 0) :
    CurveRecovery.geometricDerivativeAt K
      (algebraMap k[X] (RatFunc k) P / algebraMap k[X] (RatFunc k) Q) α =
      (P.derivative.eval₂ (algebraMap k K) α * Q.eval₂ (algebraMap k K) α -
        P.eval₂ (algebraMap k K) α * Q.derivative.eval₂ (algebraMap k K) α) /
          (Q.eval₂ (algebraMap k K) α) ^ 2 := by
  let x := algebraMap k[X] (RatFunc k) P / algebraMap k[X] (RatFunc k) Q
  have hQ0 : Q ≠ 0 := by intro hz; simp [hz] at hQ
  have hpoly : x.num * Q = P * x.denom := (RatFunc.num_mul_eq_mul_denom_iff hQ0).mpr rfl
  have hval := congrArg (Polynomial.eval₂ (algebraMap k K) α) hpoly
  simp only [eval₂_mul] at hval
  have hder := congrArg (fun p : k[X] => p.derivative.eval₂ (algebraMap k K) α) hpoly
  simp only [derivative_mul, eval₂_add, eval₂_mul] at hder
  have hD := reduced_denom_ne_zero P Q α hQ
  change x.denom.eval₂ (algebraMap k K) α ≠ 0 at hD
  change (x.num.derivative.eval₂ (algebraMap k K) α * x.denom.eval₂ (algebraMap k K) α -
      x.num.eval₂ (algebraMap k K) α * x.denom.derivative.eval₂ (algebraMap k K) α) /
      (x.denom.eval₂ (algebraMap k K) α) ^ 2 = _
  apply (div_eq_div_iff (pow_ne_zero 2 hD) (pow_ne_zero 2 hQ)).mpr
  linear_combination
    (x.denom.eval₂ (algebraMap k K) α * Q.eval₂ (algebraMap k K) α) * hder -
    (x.denom.derivative.eval₂ (algebraMap k K) α * Q.eval₂ (algebraMap k K) α +
      x.denom.eval₂ (algebraMap k K) α * Q.derivative.eval₂ (algebraMap k K) α) * hval

/-- Exact evaluation of the scheduled fresh numerator word. -/
theorem eval_word (F H : k[X]) (m : ℕ) (α : K)
    (hH : H.eval₂ (algebraMap k K) α ≠ 0) :
    RatFunc.eval (algebraMap k K) α
      ((algebraMap k[X] (RatFunc k) F) ^ m / algebraMap k[X] (RatFunc k) H) =
      F.eval₂ (algebraMap k K) α ^ m / H.eval₂ (algebraMap k K) α := by
  simpa only [map_pow, eval₂_pow] using eval_fraction (F ^ m) H α hH

/-- The scheduled tangent cross numerator computes the canonical derivative. -/
theorem derivative_word (F H : k[X]) (m : ℕ) (α : K)
    (hH : H.eval₂ (algebraMap k K) α ≠ 0) :
    CurveRecovery.geometricDerivativeAt K
      ((algebraMap k[X] (RatFunc k) F) ^ m / algebraMap k[X] (RatFunc k) H) α =
      ((m : K) * F.eval₂ (algebraMap k K) α ^ (m - 1) *
        F.derivative.eval₂ (algebraMap k K) α * H.eval₂ (algebraMap k K) α -
          F.eval₂ (algebraMap k K) α ^ m * H.derivative.eval₂ (algebraMap k K) α) /
        (H.eval₂ (algebraMap k K) α) ^ 2 := by
  simpa only [map_pow, derivative_pow, eval₂_mul, eval₂_pow, eval₂_C, eval₂_natCast, map_natCast, mul_assoc]
    using derivative_fraction (F ^ m) H α hH

/-- The pair test is actual rational-function separation, after the explicit
nonvanishing denominator hypotheses are checked. -/
theorem eval_ne_of_pair_test (F H : k[X]) (m : ℕ) (α β : K)
    (hHα : H.eval₂ (algebraMap k K) α ≠ 0) (hHβ : H.eval₂ (algebraMap k K) β ≠ 0)
    (ht : SeparationExclusions.Test.Holds (F.map (algebraMap k K))
      (.pair α β m (H.map (algebraMap k K)))) :
    RatFunc.eval (algebraMap k K) α
      ((algebraMap k[X] (RatFunc k) F) ^ m / algebraMap k[X] (RatFunc k) H) ≠
    RatFunc.eval (algebraMap k K) β
      ((algebraMap k[X] (RatFunc k) F) ^ m / algebraMap k[X] (RatFunc k) H) := by
  rw [eval_word F H m α hHα, eval_word F H m β hHβ]
  intro heq
  have hc : F.eval₂ (algebraMap k K) α ^ m * H.eval₂ (algebraMap k K) β -
      F.eval₂ (algebraMap k K) β ^ m * H.eval₂ (algebraMap k K) α ≠ 0 := by
    simpa only [SeparationExclusions.Test.Holds, eval_map] using ht
  exact hc (sub_eq_zero.mpr ((div_eq_div_iff hHα hHβ).mp heq))

/-- The tangent test is actual nonvanishing of the canonical rational derivative. -/
theorem derivative_ne_zero_of_tangent_test (F H : k[X]) (m : ℕ) (α : K)
    (hH : H.eval₂ (algebraMap k K) α ≠ 0)
    (ht : SeparationExclusions.Test.Holds (F.map (algebraMap k K))
      (.tangent α m (H.map (algebraMap k K)))) :
    CurveRecovery.geometricDerivativeAt K
      ((algebraMap k[X] (RatFunc k) F) ^ m / algebraMap k[X] (RatFunc k) H) α ≠ 0 := by
  rw [derivative_word F H m α hH]
  apply div_ne_zero _ (pow_ne_zero 2 hH)
  simpa only [SeparationExclusions.Test.Holds, eval_map, derivative_map] using ht

/-- A coprime polynomial fraction retains every denominator factor after
canonical reduction, even when the denominator is not monic. -/
theorem denominator_dvd_reduced (P Q : k[X]) (hQ : Q ≠ 0) (hPQ : IsCoprime P Q) :
    Q ∣ (algebraMap k[X] (RatFunc k) P / algebraMap k[X] (RatFunc k) Q).denom := by
  let x := algebraMap k[X] (RatFunc k) P / algebraMap k[X] (RatFunc k) Q
  have hrel : x.num * Q = P * x.denom := (RatFunc.num_mul_eq_mul_denom_iff hQ).mpr rfl
  exact hPQ.symm.dvd_of_dvd_mul_left (hrel ▸ dvd_mul_left Q x.num)

/-- A prescribed old raw factor remains an actual finite pole of a coprime word. -/
theorem factor_dvd_word_denom (F H p : k[X]) (m : ℕ)
    (hH : H ≠ 0) (hcoprime : IsCoprime (F ^ m) H) (hp : p ∣ H) :
    p ∣ ((algebraMap k[X] (RatFunc k) F) ^ m / algebraMap k[X] (RatFunc k) H).denom := by
  simpa only [map_pow] using hp.trans (denominator_dvd_reduced (F ^ m) H hH hcoprime)

/-- The degree inequality for an unreduced scheduled fraction is exactly a
pole at infinity after canonical reduction. -/
theorem word_pole_at_infinity (F H : k[X]) (m : ℕ) (hF : F ≠ 0) (hH : H ≠ 0)
    (hdegree : H.natDegree < m * F.natDegree) :
    ((algebraMap k[X] (RatFunc k) F) ^ m / algebraMap k[X] (RatFunc k) H).denom.natDegree <
      ((algebraMap k[X] (RatFunc k) F) ^ m / algebraMap k[X] (RatFunc k) H).num.natDegree := by
  let x := (algebraMap k[X] (RatFunc k) F) ^ m / algebraMap k[X] (RatFunc k) H
  have hpositive : (0 : ℤ) < x.intDegree := by
    dsimp [x]
    rw [← map_pow, RatFunc.intDegree_div (RatFunc.algebraMap_ne_zero (pow_ne_zero m hF))
      (RatFunc.algebraMap_ne_zero hH), RatFunc.intDegree_polynomial, RatFunc.intDegree_polynomial,
      natDegree_pow]
    apply sub_pos.mpr
    exact_mod_cast hdegree
  rw [RatFunc.intDegree] at hpositive
  have hnat : x.denom.natDegree < x.num.natDegree := by exact_mod_cast (sub_pos.mp hpositive)
  simpa only [x, map_pow] using hnat

end UnconditionalCounterexample.RationalFunctionJets
