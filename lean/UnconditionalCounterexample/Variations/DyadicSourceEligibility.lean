import UnconditionalCounterexample.Variations.DyadicTaskSource
import UnconditionalCounterexample.Variations.DyadicPrefixEligibility

/-! # Existence of the finite instruction at every eligible split opening -/

noncomputable section
namespace UnconditionalCounterexample.Variations.DyadicLedger.Calibrated
open Univariate DiscreteOrders

/-- The data used by the planner exist on the actual prefix of its own
selector whenever the scheduled element is integral and has positive height
at both centres. The new auxiliary column list can be arbitrary. -/
theorem task_has_prepared (a : Policy) (r : ℕ) (hx : (taskAt r).element ≠ 0)
    (hA : (taskAt r).element ∈ domain (driver a).requirements)
    (h₀ : 0 < order (valuation a (.centre false)) (taskAt r).element)
    (h₁ : 0 < order (valuation a (.centre true)) (taskAt r).element) (aux : List RawColumn) :
    let D := driver a
    let n := D.opening (r+1)
    Nonempty (PrefixInstruction.Prepared (D.state n) ((chain D.requirements).approx n)
      (table D.requirements n) aux (Units.mk0 _ hx)) := by
  let D := driver a
  let n := D.opening (r+1)
  have hn : 0 < n := D.opening_strict (Nat.zero_lt_succ r)
  exact PrefixInstruction.exists_prepared _ _ _ _ _ (prefix_uniqueRegular a n)
    (prefix_mass_of_exterior a n _ (task_exterior a r hx))
    (prefix_effective a n _ hA (prefix_uniqueRegular a n)) h₀ h₁ (prefix_coarse_mass a n hn)

end UnconditionalCounterexample.Variations.DyadicLedger.Calibrated
