import UnconditionalCounterexample.MixedSelectionEstimates
import UnconditionalCounterexample.MixedSequenceArguments

/-! # Uniform estimates along the mixed sequence at every actual prime -/

noncomputable section
namespace UnconditionalCounterexample.MixedLocalTransfer
open Polynomial Filter ConstructionWords MixedStageRecursion CombinedGuardStep
open PrimaryChoices GuardSupport LocalAlgebra MixedStageSelection MixedWordTransfer MixedSequenceArguments
variable {R : Requirements}

set_option backward.isDefEq.respectTransparency false in
/-- Every fixed prime and scale eventually has all ordinary word-derivative
bounds and actual scaled-ring transfer identities for the same global raw sequence.
Raw stage n has the manuscript's positive arithmetic precision n+1. -/
theorem eventually_all_word_estimates (seq : Sequence R) (j s : ℕ) :
    ∀ᶠ n in atTop, ∀ w : Word n,
      (∀ b : Bool, Active (R.primary.paired (primes j)) b → (LocalInterpolation.wordDerivative
        ((seq.chain.raw n).map (algebraMap ℚ ℚ_[(primes j).val]))
        (((MixedGlobalPlans.globalPlan seq n).wordDen w).map (algebraMap ℚ ℚ_[(primes j).val]))
        w.latestExponent (branch seq j b)).valuation < -((n + 1 : ℕ) : ℤ)) ∧
      ∃ U V : padicScaledPolynomialRing (primes j).val s,
        (RatFunc.C ((primes j).val : ℚ_[(primes j).val]) ^ (2 * s) *
          (vanishing (R.primary.paired (primes j)) (branch seq j))) ^ w.latestExponent =
          RatFunc.C ((primes j).val : ℚ_[(primes j).val]) ^ (n + 1) *
            ((U : RatFunc ℚ_[(primes j).val]) + (V : RatFunc ℚ_[(primes j).val]) *
              (((seq.chain.raw n).map (algebraMap ℚ ℚ_[(primes j).val]) :
                RatFunc ℚ_[(primes j).val]) ^ w.latestExponent /
                (((MixedGlobalPlans.globalPlan seq n).wordDen w).map
                  (algebraMap ℚ ℚ_[(primes j).val]) : RatFunc ℚ_[(primes j).val]))) := by
  filter_upwards [eventually_mem_indices seq j, eventually_ge_atTop s] with n hj hs
  intro w
  constructor
  · intro b hb
    have h := selection_word_derivative (seq.selection n) ⟨j, hj⟩ w b hb
    simpa only [selection_branch_eq, Batch.primeAt, ← MixedGlobalPlans.globalRaw_eq_selection,
      ← MixedGlobalPlans.globalPlan_wordDen] using h
  · have hbranch : R.primary.branch (seq.selection n).batch ⟨j,hj⟩ = branch seq j :=
      funext (selection_branch_eq seq n ⟨j,hj⟩)
    have h := selection_word_transfer (seq.selection n) ⟨j, hj⟩ s (by omega) w
    simpa only [hbranch, Batch.primeAt, ← MixedGlobalPlans.globalRaw_eq_selection,
      ← MixedGlobalPlans.globalPlan_wordDen] using h


end UnconditionalCounterexample.MixedLocalTransfer
