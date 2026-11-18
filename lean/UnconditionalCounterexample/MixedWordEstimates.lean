import UnconditionalCounterexample.MixedConductor
import UnconditionalCounterexample.MixedLocalTransfer

/-!
# Actual producers of the mixed conductor word estimates

The global prime enumeration is reindexed to each literal rational prime
before specializing to a selected primary. This preserves the p-adic field
and avoids assigning a primary argument outside the selected set.
-/

noncomputable section
namespace UnconditionalCounterexample.MixedWordEstimates

open Polynomial Filter GuardSupport ConstructionWords MixedConstruction MixedConductor
open LocalAlgebra

variable (S : Set PrimeIndex) (hS : S.Infinite)

noncomputable def branch (p : PrimeIndex) (b : Bool) : ℚ_[p.val] :=
  SparsePrimaryDomain.branchAt (primeEmbedding S hS)
    (SelectedPrimes.primary (SelectedPrimes.primes S hS)) p ((places S hS).guard p) b

@[simp] theorem branch_true (p : PrimeIndex) :
    branch S hS p true = ((places S hS).guard p).val := rfl

@[simp] theorem branch_selected_false (j : ℕ) :
    branch S hS ((places S hS).primes j) false = ((places S hS).primary j).val :=
  SparsePrimaryDomain.branchAt_false_prime (primeEmbedding S hS)
    (SelectedPrimes.primary (SelectedPrimes.primes S hS)) j _

theorem branch_global (j : ℕ) :
    branch S hS (PrimaryChoices.primes j) =
      MixedSequenceArguments.branch (construction S hS) j := by
  funext b
  cases b <;> rfl

/-- Reindex the actual estimates by a literal prime, with the actual active
argument predicate and the same global polynomial fraction. -/
theorem eventually_all_at_prime (p : PrimeIndex) (s : ℕ) :
    ∀ᶠ n in atTop, ∀ w : Word n,
      (∀ b : Bool, MixedStageSelection.Active (p ∈ S) b →
        (wordDerivative S hS p n w (branch S hS p b)).valuation < -((n + 1 : ℕ) : ℤ)) ∧
      ∃ U V : padicScaledPolynomialRing p.val s,
        (RatFunc.C (p.val : ℚ_[p.val]) ^ (2*s) *
          MixedWordTransfer.vanishing (p ∈ S) (branch S hS p)) ^ w.latestExponent =
        RatFunc.C (p.val : ℚ_[p.val]) ^ (n+1) *
          ((U : RatFunc ℚ_[p.val]) + (V : RatFunc ℚ_[p.val]) * wordValue S hS p n w) := by
  obtain ⟨j, rfl⟩ := PrimaryChoices.primes.surjective p
  simpa only [wordDerivative, wordValue, wordDen, branch_global,
    MixedConstruction.requirements, MixedConstruction.paired_iff] using
    MixedLocalTransfer.eventually_all_word_estimates (construction S hS) j s

/-- Every field of the intermediate conductor contract is supplied by the
actual mixed recursive construction, with no remaining arithmetic hypothesis. -/
theorem wordEstimates : WordEstimates S hS := by
  constructor
  · intro j
    have hj : (places S hS).primes j ∈ S := by
      have hi : (places S hS).primes j ∈ Set.range (places S hS).primes := ⟨j, rfl⟩
      simpa only [selected_range S hS] using hi
    filter_upwards [eventually_all_at_prime S hS ((places S hS).primes j) 0] with n hn
    intro w
    simpa only [branch_selected_false] using (hn w).1 false (Or.inr hj)
  · intro p
    filter_upwards [eventually_all_at_prime S hS p 0] with n hn
    intro w
    simpa only [branch_true] using (hn w).1 true (Or.inl rfl)
  · intro j s
    have hj : (places S hS).primes j ∈ S := by
      have hi : (places S hS).primes j ∈ Set.range (places S hS).primes := ⟨j, rfl⟩
      simpa only [selected_range S hS] using hi
    filter_upwards [eventually_all_at_prime S hS ((places S hS).primes j) s] with n hn
    intro w
    simpa only [MixedWordTransfer.vanishing_pair hj, branch_selected_false, branch_true] using (hn w).2
  · intro p hp s
    filter_upwards [eventually_all_at_prime S hS p s] with n hn
    intro w
    simpa only [MixedWordTransfer.vanishing_single hp, branch_true] using (hn w).2

end UnconditionalCounterexample.MixedWordEstimates
