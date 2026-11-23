import UnconditionalCounterexample.Variations.DyadicScheduledProfiles
import UnconditionalCounterexample.Variations.DyadicNamedPair

/-!
# A hereditarily atomic domain with a pair having no maximal common divisor

The domain, its two named witnesses, and the split for every eligible element
and positive modulus all use the same univariate polynomial sequence. In
particular the domain fails strong atomicity and weak ACCP.
-/

noncomputable section
namespace UnconditionalCounterexample.Variations.DyadicCounterexample
open DyadicLedger DyadicLedger.Calibrated DyadicLedger.ScheduledSplit
open DiscreteOrders

/-- The split-aware calibrated domain inside the rational function field. -/
abbrev ring := Univariate.domain ScheduledSplit.run.requirements

/-- The two factors split the centre heights, with the coprime return
congruences over every positive integer modulus. -/
theorem splits : HasSplits ScheduledSplit.policy ring :=
  hasSplits_of_profiled profiled

theorem hereditarilyAtomic : Factorization.IsHereditarilyAtomic ring :=
  hereditary_of_splits ScheduledSplit.policy splits

/-- The first common tail begins after the plus entry two at index zero. -/
def x : ring := pairElement ScheduledSplit.policy false

/-- The second plus profile has entry four at index one. -/
def y : ring := pairElement ScheduledSplit.policy true

/-- Every common divisor extends strictly within the same concrete domain. -/
theorem pair_extension {d : ring} (hdx : d ∣ x) (hdy : d ∣ y) :
    ∃ u : ring, ¬ IsUnit u ∧ d*u ∣ x ∧ d*u ∣ y :=
  pairElement_extend ScheduledSplit.policy hdx hdy

/-- Hereditary atomicity and the two factorization failures for a single
explicit subring and a single explicit nonzero pair. -/
theorem counterexample :
    Factorization.IsHereditarilyAtomic ring ∧ x ≠ 0 ∧ y ≠ 0 ∧
      (∀ d : ring, d ∣ x → d ∣ y → ∃ u : ring, ¬ IsUnit u ∧ d*u ∣ x ∧ d*u ∣ y) ∧
      ¬ Factorization.IsStronglyAtomicDomain ring ∧ ¬ Factorization.IsWeakACCP ring :=
  ⟨hereditarilyAtomic,pairElement_ne_zero ScheduledSplit.policy false,pairElement_ne_zero ScheduledSplit.policy true,
   fun _ => pair_extension,(domain_pair_obstruction ScheduledSplit.policy).2⟩

end UnconditionalCounterexample.Variations.DyadicCounterexample
