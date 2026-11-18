import UnconditionalCounterexample.PaperAtoms
import UnconditionalCounterexample.ReturnChain
import UnconditionalCounterexample.ReturnCongruences
import UnconditionalCounterexample.SequenceValuations

/-!
# Actual return congruences in the constructed domain

The same selected q polynomial gives the return estimate for the literal
canonical recurrence. Each fixed prime is processed at every sufficiently
late stage. The proved primary and guard profiles then force the refined
target on both branches. Their growing p-adic precision implies eventual
divisibility of a_n-1 by every positive integer inside the fixed domain.
-/

noncomputable section
namespace UnconditionalCounterexample.ConstructionReturns
open Polynomial Filter PrimaryTargets RecursivePrefix ConstructionWords PaperConstruction

/-- At the actual selected q-stage, every refined processed branch gives the
return congruence for the actual global a_(n+1). -/
theorem q_return_selected (n : ℕ) :
    let s := construction.selection (2 * n + 2)
    ∀ i : s.batch.indices, ∀ β : Bool,
      ReturnTargets.IsRefined (branchOrder (2 * n + 2) i.val β)
        (EvaluationDVR.evaluationHom (s.batch.primeAt i) (s.batch.branch i β)
          (s.batch.branch_transcendental i β)
          (construction.chain.a n * construction.chain.b (n + 1))) →
      (EvaluationDVR.evaluationHom (s.batch.primeAt i) (s.batch.branch i β)
          (s.batch.branch_transcendental i β) (construction.chain.a (n + 1)) - 1) /
        (s.batch.primeAt i : ℚ_[s.batch.primeAt i]) ^ n ∈ PadicInt.subring (s.batch.primeAt i) := by
  dsimp only
  let s := construction.selection (2 * n + 2)
  let P := construction.chain.approx (2 * n + 2)
  let hc : Choice s.batch.primeAt s.batch.auxiliary.val s.plan s.batch.branch
      (fun i β => P.qTarget n (s.batch.primeAt i) (s.batch.branch i β)
        (s.batch.branch_transcendental i β) (branchOrder (2 * n + 2) i.val β))
      (fun i β => P.qPrecision n (s.batch.primeAt i) (s.batch.branch i β)
        (s.batch.branch_transcendental i β) (branchOrder (2 * n + 2) i.val β)) := by
    refine ⟨s.choice.N, s.choice.coeff, s.choice.positive_multiple, ?_⟩
    simpa only [requirements, targets, generatorAt_even_succ,
      Prefix.generatorTarget, Prefix.generatorPrecision] using s.choice.witnesses
  have hlocal := ReturnPrefix.choice_q_actual s.batch.primeAt s.batch.auxiliary.val n
    P s.plan s.batch.branch s.batch.branch_transcendental
    (fun i β => branchOrder (2 * n + 2) i.val β) hc s.toNext rfl rfl
  intro i β href
  have h := (hlocal i β).2
  dsimp only [P] at h
  rw [construction.chain.a_agrees_before_q n, construction.chain.b_succ_agrees_before_q n] at h
  have hnext : construction.chain.next (2 * n + 2) = s.toNext := construction.consistent _
  rw [← hnext, ← construction.chain.a_succ_eq_appended n] at h
  exact h href

end UnconditionalCounterexample.ConstructionReturns

namespace UnconditionalCounterexample.ConstructionReturns
open Polynomial Filter PrimaryTargets RecursivePrefix ConstructionWords PaperConstruction

/-- The selected branch congruence is a congruence in the actual global
intersection evaluation, because assigned guards are preserved literally. -/
theorem q_return_processed (n j : ℕ) (β : Bool)
    (hj : PrimaryChoices.primes j ∈ (construction.selection (2 * n + 2)).batch.processed.primes)
    (href : ReturnTargets.IsRefined (branchOrder (2 * n + 2) j β)
      (PairedDomain.evaluationBranch places j β
        (construction.chain.a n * construction.chain.b (n + 1)))) :
    (PairedDomain.evaluationBranch places j β (construction.chain.a (n + 1)) - 1) /
      ((places.primes j).val : ℚ_[(places.primes j).val]) ^ n ∈
        PadicInt.subring (places.primes j).val := by
  let s := construction.selection (2 * n + 2)
  let i : s.batch.indices := ⟨j, (s.batch.mem_indices j).mpr hj⟩
  have h := q_return_selected n i β
  rw [SequenceValuations.branch_evaluation_agrees construction (2 * n + 2) i β] at h
  exact h href

/-- Multiplicative valuation one means exactly norm one. -/
theorem norm_eq_one_of_mulValuation_eq_one {p : ℕ} [Fact p.Prime]
    (z : ℚ_[p]) (hz : Padic.mulValuation z = 1) : ‖z‖ = 1 := by
  have hn : z ≠ 0 := by
    intro h
    simp only [h, map_zero, zero_ne_one] at hz
  rw [Padic.norm_eq_zpow_log_mulValuation hn, hz, WithZero.log_one, zpow_zero]

end UnconditionalCounterexample.ConstructionReturns

namespace UnconditionalCounterexample.ConstructionReturns
open Polynomial Filter PrimaryTargets RecursivePrefix ConstructionWords PaperConstruction

/-- Once j lies below the moving primary support, the exact earlier product
used in the q-stage refinement has unit norm on both actual branches. -/
theorem prior_product_norm_one (n j : ℕ) (hj : j < 2 * n) (β : Bool) :
    ‖PairedDomain.evaluationBranch places j β
      (construction.chain.a n * construction.chain.b (n + 1))‖ = 1 := by
  apply norm_eq_one_of_mulValuation_eq_one
  cases β with
  | false =>
    have ha := AtomProfiles.a_primary raw exponent places generatorProfiles PrimaryChoices.primary_zero n j
    have hb := generator_b_valuation (n + 1) j
    rw [primaryAtomProfile_of_lt hj] at ha
    have hjb : j ≠ 2 * (n + 1) := by omega
    simp only [PrimaryWordProfiles.bWeight, hjb, ite_false, neg_zero, WithZero.exp_zero] at hb
    simp only [neg_zero, WithZero.exp_zero] at ha
    change PairedDomain.vertical places (.inl j)
      (construction.chain.a n * construction.chain.b (n + 1)) = 1
    rw [map_mul]
    change PairedDomain.vertical places (.inl j) (ReturnPrefix.a (CompleteProfiles.generators raw exponent) n) *
      PairedDomain.vertical places (.inl j)
        (CompleteProfiles.generators raw exponent (NormalizedWords.Generator.b (n + 1)).stage) = 1
    rw [ha, hb, one_mul]
  | true =>
    have ha := AtomProfiles.a_guard raw exponent places generatorProfiles
      construction.chain.guardChain.value_unit n (places.primes j)
    have hb := generator_guard_valuation (NormalizedWords.Generator.b (n + 1)).stage (places.primes j)
    change PairedDomain.vertical places (.inr (places.primes j))
      (construction.chain.a n * construction.chain.b (n + 1)) = 1
    rw [map_mul]
    change PairedDomain.vertical places (.inr (places.primes j))
        (ReturnPrefix.a (CompleteProfiles.generators raw exponent) n) *
      PairedDomain.vertical places (.inr (places.primes j))
        (CompleteProfiles.generators raw exponent (NormalizedWords.Generator.b (n + 1)).stage) = 1
    rw [ha, hb, one_mul]

theorem q_branchOrder_zero (n j : ℕ) (hj : j < 2 * n) (β : Bool) :
    branchOrder (2 * n + 2) j β = 0 := by
  cases β with
  | true => rfl
  | false =>
    rw [branchOrder_false, primaryOrder_even_succ]
    split_ifs <;> omega

/-- Every fixed prime and both its actual branches eventually receive the
refined q target, with the prescribed growing return precision. -/
theorem eventually_refined_returns (j : ℕ) (β : Bool) :
    ∀ᶠ n : ℕ in atTop,
      (PairedDomain.evaluationBranch places j β (construction.chain.a (n + 1)) - 1) /
        ((places.primes j).val : ℚ_[(places.primes j).val]) ^ n ∈
          PadicInt.subring (places.primes j).val := by
  filter_upwards [eventually_ge_atTop (max (j + 1) (PrimaryChoices.primes j).val)] with n hn
  have hj : j < 2 * n := by omega
  have hp := SequenceValuations.processed_of_le construction (2 * n + 2)
    (PrimaryChoices.primes j) (by omega)
  apply q_return_processed n j β hp
  exact ⟨q_branchOrder_zero n j hj β, prior_product_norm_one n j hj β⟩

end UnconditionalCounterexample.ConstructionReturns

namespace UnconditionalCounterexample.ConstructionReturns
open Filter PaperConstruction

/-- The literal atoms from the fixed simultaneous construction approach one
modulo every positive integer inside that very same domain. -/
theorem eventually_integer_dvd_atom_sub_one (m : ℕ) (hm : 0 < m) :
    ∀ᶠ n : ℕ in atTop, (m : PaperConstruction.domain) ∣ PaperConstruction.atom n - 1 := by
  apply PairedDomain.eventually_integer_dvd_of_refined_returns places poles atom _ m hm
  intro j β
  simpa only [PaperConstruction.coe_atom] using eventually_refined_returns j β

end UnconditionalCounterexample.ConstructionReturns
