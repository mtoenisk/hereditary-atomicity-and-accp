import UnconditionalCounterexample.Variations.UnivariateRecovery
import UnconditionalCounterexample.HorizontalOrders
import UnconditionalCounterexample.RationalSigns

/-!
# Signed words on the adaptive univariate curve

A rational function with trivial orders at the retained horizontal primes is a
pole-algebra unit. At every permanent guard, valuation one removes the rational
scalar in its factorization, provided the generators have valuation one there.
The guard valuations have finite support on each nonzero rational function.
-/

noncomputable section
namespace UnconditionalCounterexample.Variations.UnivariateExtraction

open Polynomial WithZero GuardSupport Univariate PrincipalProfiles

variable (R : Requirements)

abbrev generator := ScheduledRecovery.generators (chain R).raw (chain R).exponent

/-- Each permanent guard is the one selected by the guard chain. -/
abbrev guardHom (p : PrimeIndex) : RatFunc ℚ →+* ℚ_[p.val] :=
  guardEvaluation (chain R).guardChain.value (chain R).guardChain.value_transcendental p

abbrev guardVal (p : PrimeIndex) := EvaluationDVR.valuation p.val (guardHom R p)

theorem guard_support (x : RatFunc ℚ) (hx : x ≠ 0) :
    {p : PrimeIndex | guardVal R p x ≠ 1}.Finite :=
  (chain R).guardChain.ratFunc_guardSupport_finite x hx

theorem eval_permanent_guard (p : PrimeIndex) (x : RatFunc ℚ) :
    LocalEvaluation.evalAt (permanentSite R p).guard.val (permanentSite R p).guard_trans x =
      guardHom R p x := by
  change LocalEvaluation.evalAt _ _ x = LocalEvaluation.evalAt _ _ x
  congr 2
  exact congrArg Subtype.val (permanent_guard_eq R p)

theorem signed_word_of_horizontal_units (hG : ∀ p i, guardVal R p (generator R i) = 1)
    (x : RatFunc ℚ) (hx : x ≠ 0)
    (hhoriz : ∀ q, HorizontalOrders.Retained (poles R) q → HorizontalOrders.valuation q x = 1)
    (hguard : ∀ p, guardVal R p x = 1) :
    ∃ e : ℕ →₀ ℤ, x = word (generator R) e ∨ x = -word (generator R) e := by
  have hunit := (HorizontalOrders.mem_and_inv_mem_iff_retained_valuations_eq_one
    (poles R) (poles_nonzero R) x hx).mpr hhoriz
  exact RationalSigns.exists_signed_normalized_factorization (chain R).raw
    (fun n => ⟨(chain R).raw_monic n, (chain R).raw_irreducible n⟩)
    (fun _ _ h => (chain R).raw_degree_strict.injective (congrArg natDegree h))
    (chain R).exponent x hx hunit.1 hunit.2 (guardHom R) hguard hG

end UnconditionalCounterexample.Variations.UnivariateExtraction
