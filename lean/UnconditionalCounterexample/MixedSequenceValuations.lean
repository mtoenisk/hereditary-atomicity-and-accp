import UnconditionalCounterexample.MixedStageRecursion
import UnconditionalCounterexample.MixedSequenceArguments
import UnconditionalCounterexample.ReturnChain
import UnconditionalCounterexample.RawEvaluationPromises
import UnconditionalCounterexample.MixedReturnPrefix

/-!
# The literal valuation columns of one mixed construction

All raw polynomials, powers, finite batches and global guard values come from
one MixedStageRecursion.Sequence. The selector witnesses supply current normalized
profiles and the auxiliary model; batch progress supplies later guard units.
Only active branches carry selector conditions, and primary orders are indexed
by actual selected rational primes. The finite target policy's norms/support
remain as TargetNorms. Outside
current processing, signed constants and coefficient support imply raw primary
units, and nested processing sets handle every old denominator factor.
-/

namespace UnconditionalCounterexample.MixedSequenceValuations

open Polynomial GuardSupport PaperGuardStages CombinedGuardStep RecursivePrefix ConstructionWords
  MixedStageRecursion RawEvaluationPromises PrimaryChoices

variable {R : Requirements} (S : Sequence R)

theorem evaluationHom_congr (p : ℕ) [Fact p.Prime] {a b : ℚ_[p]}
    (ha : Transcendental ℚ a) (hb : Transcendental ℚ b) (h : a = b) :
    EvaluationDVR.evaluationHom p a ha = EvaluationDVR.evaluationHom p b hb := by
  subst b
  rfl

theorem evaluationValuation_congr (p : ℕ) [Fact p.Prime] {a b : ℚ_[p]}
    (ha : Transcendental ℚ a) (hb : Transcendental ℚ b) (h : a = b) :
    EvaluationDVR.evaluationValuation p a ha = EvaluationDVR.evaluationValuation p b hb := by
  subst b
  rfl

noncomputable def generators : ℕ → RatFunc ℚ := ScheduledRecovery.generators S.chain.raw S.chain.exponent

theorem raw_eq_selection (n : ℕ) : S.chain.raw n = (S.selection n).raw := by
  rw [S.chain.raw_eq_selected, S.consistent]
  rfl

theorem exponent_eq_selection (n : ℕ) : S.chain.exponent n = (S.selection n).plan.E := by
  rw [S.chain.exponent_eq_selected, S.consistent]
  rfl

theorem batch_eq_selection (n : ℕ) : S.chain.batch n = (S.selection n).batch :=
  MixedSequenceArguments.sequence_batch_eq_selection S n

theorem assignment_eq_selection (n : ℕ) :
    S.chain.guardChain.assignments n = (S.selection n).batch.assigned :=
  MixedSequenceArguments.assignment_eq_selection S n

theorem denominator_eq_plan (n : ℕ) :
    rawDenominator S.chain.raw S.chain.exponent n = (S.selection n).plan.rawDen := by
  unfold rawDenominator DegreePlan.rawDen
  rw [← Finset.prod_pow, exponent_eq_selection]
  apply Finset.prod_congr rfl
  intro j _
  rw [S.chain.rawAt_agrees n j.val j.isLt]

theorem generators_eq_quotient (n : ℕ) :
    generators S n = algebraMap ℚ[X] (RatFunc ℚ) (S.chain.raw n) /
      algebraMap ℚ[X] (RatFunc ℚ) (rawDenominator S.chain.raw S.chain.exponent n) := by
  unfold generators ScheduledRecovery.generators RawWords.normalizedFactor rawDenominator
  dsimp only
  rw [← Finset.prod_pow, Fin.prod_univ_eq_prod_range (fun j => S.chain.raw j ^ S.chain.exponent n) n, map_prod]
  simp only [map_pow]

theorem prefix_generators_agrees (n j : ℕ) (hj : j < n) :
    (S.chain.approx n).generators j = generators S j := by
  apply ReturnPrefix.generators_congr
  · intro k hk
    exact S.chain.rawAt_agrees n k (lt_of_le_of_lt hk hj)
  · exact S.chain.exponentAt_agrees n j hj

theorem appended_generator_agrees (n : ℕ) :
    (S.selection n).toNext.append.generators n = generators S n := by
  rw [← S.consistent, ← S.chain.step]
  exact prefix_generators_agrees S (n + 1) n (by omega)

/-- The actual current-stage local selector controls the same global generator. -/
theorem processed_norm (n : ℕ) (i : (S.selection n).batch.indices) (b : Bool)
    (hb : MixedStageSelection.Active (R.primary.paired (primes i.val)) b) :
    ‖EvaluationDVR.evaluationHom ((S.selection n).batch.primeAt i)
      (R.primary.branch (S.selection n).batch i b)
      (R.primary.branch_transcendental (S.selection n).batch i b hb)
      (generators S n)‖ = ‖(R.targets (S.chain.approx n) (S.selection n).batch).value i b‖ := by
  have hn := MixedReturnPrefix.choice_actual_norm (S.selection n).batch.primeAt
    (fun i => R.primary.paired (primes i.val))
    (S.selection n).batch.auxiliary.val n (S.chain.approx n) (S.selection n).plan
    (R.primary.branch (S.selection n).batch) _
    (R.primary.branch_transcendental (S.selection n).batch) _
    (S.selection n).choice (S.selection n).toNext rfl rfl i b hb
  rw [appended_generator_agrees] at hn
  exact hn

/-- Later first-assignment avoidance is supplied by the actual batch transition. -/
theorem later_raw_norm (k : ℕ) (p : PrimeIndex)
    (hp : p ∈ (S.chain.guardChain.assignments (k + 1)).primes)
    (hn : p ∉ (S.chain.guardChain.assignments k).primes) (j : ℕ) (hj : j ≤ k) :
    ‖(S.chain.raw j).eval₂ (algebraMap ℚ ℚ_[p.val])
      ((S.chain.guardChain.assignments (k + 1)).guard p hp).value.val‖ = 1 := by
  have hp' : p ∈ (S.selection (k + 1)).batch.assigned.primes := by
    simpa only [assignment_eq_selection] using hp
  have hn' : p ∉ (S.chain.approx (k + 1)).state.assignment.primes := hn
  have h := ((S.selection (k + 1)).progress.new_guard p hp' hn').2 ⟨j, by omega⟩
  rw [S.chain.raw_agrees] at h
  simpa only [assignment_eq_selection] using h

/-- The current auxiliary guard uses the selected polynomial's actual shifted model. -/
theorem auxiliary_raw_norm (n : ℕ) :
    ‖(S.chain.raw n).eval₂ (algebraMap ℚ ℚ_[(S.selection n).batch.auxiliary.val])
      (S.selection n).batch.auxiliary_guard.value.val‖ = 1 := by
  obtain ⟨G, _, hmap, hred, _⟩ := (S.selection n).choice.witnesses.2.2.2.2.2.2.2
  rw [raw_eq_selection]
  exact current_auxiliary_norm_one_of_shifted_model (S.selection n).batch (S.selection n).raw
    G ((S.selection n).plan.degree - 1 + 1) hmap hred

/-- The b/q targets supply the prescribed norms and finite primary support. All polynomial/guard facts come
from this same sequence's actual selector witnesses. -/
structure TargetNorms (order : ℕ → PrimeIndex → ℕ) : Prop where
  norm : ∀ (n : ℕ) (i : (S.selection n).batch.indices) (b : Bool)
    (_hb : MixedStageSelection.Active (R.primary.paired (primes i.val)) b),
    ‖(R.targets (S.chain.approx n) (S.selection n).batch).value i b‖ =
      ((S.selection n).batch.primeAt i : ℝ) ^ (-(if b then 0 else (order n (primes i.val) : ℤ)))
  support : ∀ n p, order n p ≠ 0 → p ∈ R.needed n

variable {order : ℕ → PrimeIndex → ℕ}

theorem processed_guard_norm (ht : TargetNorms S order) (n : ℕ) (p : PrimeIndex)
    (hp : p ∈ (S.selection n).batch.processed.primes) :
    ‖(S.chain.raw n).eval₂ (algebraMap ℚ ℚ_[p.val])
      ((S.selection n).batch.processed.guard p hp).value.val /
      (rawDenominator S.chain.raw S.chain.exponent n).eval₂ (algebraMap ℚ ℚ_[p.val])
        ((S.selection n).batch.processed.guard p hp).value.val‖ = 1 := by
  obtain ⟨j, rfl⟩ := primes.surjective p
  let i : (S.selection n).batch.indices := ⟨j, ((S.selection n).batch.mem_indices j).mpr hp⟩
  have hn := processed_norm S n i true (Or.inl rfl)
  rw [ht.norm n i true (Or.inl rfl), generators_eq_quotient, ReturnTargets.evaluation_normalized_polynomial] at hn
  simp only [ite_true, neg_zero, zpow_zero] at hn
  exact hn

theorem raw_guard_norm (ht : TargetNorms S order) (n : ℕ) (p : PrimeIndex) :
    ‖(S.chain.raw n).eval₂ (algebraMap ℚ ℚ_[p.val]) (S.chain.guardChain.value p).val‖ = 1 :=
  raw_norm_one_of_normalized_stage_promises S.chain.guardChain
    (fun n => (S.selection n).batch) (assignment_eq_selection S)
    S.chain.raw S.chain.exponent (processed_guard_norm S ht) (auxiliary_raw_norm S) (later_raw_norm S) n p

theorem generator_guard_valuation (ht : TargetNorms S order) (n : ℕ) (p : PrimeIndex) :
    EvaluationDVR.valuation p.val
      (guardEvaluation S.chain.guardChain.value S.chain.guardChain.value_transcendental p)
      (generators S n) = 1 := by
  rw [generators_eq_quotient]
  exact normalized_guard_valuation_one S.chain.guardChain S.chain.raw S.chain.exponent
    (raw_guard_norm S ht) n p

/-- Every earlier completed batch, including its auxiliary prime, is contained
in the next ordinary processing set. -/
theorem earlier_assigned_subset_processed (k n : ℕ) (hkn : k < n) :
    (S.selection k).batch.assigned.primes ⊆ (S.selection n).batch.processed.primes := by
  intro p hp
  have hp' : p ∈ ((S.chain.approx n).batch ⟨k, hkn⟩).assigned.primes := by
    rw [S.chain.batch_agrees, batch_eq_selection]
    exact hp
  have hm := (S.chain.approx n).assigned_subset ⟨k, hkn⟩ hp'
  rw [(S.selection n).progress.processed]
  exact Finset.mem_union_left _ (Finset.mem_union_left _ hm)

theorem earlier_processed_subset (k n : ℕ) (hkn : k < n) :
    (S.selection k).batch.processed.primes ⊆ (S.selection n).batch.processed.primes :=
  (S.selection k).batch.processed_subset_assigned.trans (earlier_assigned_subset_processed S k n hkn)

/-- Outside the actual processing set, the selected signed constant is a unit. -/
theorem raw_constant_norm (n : ℕ) (p : PrimeIndex)
    (hp : p ∉ (S.selection n).batch.processed.primes) :
    ‖((S.chain.raw n).coeff 0 : ℚ_[p.val])‖ = 1 := by
  rw [raw_eq_selection, show (S.selection n).raw.coeff 0 = (S.selection n).constant from
    (S.selection n).choice.witnesses.2.2.1]
  apply SignedConstant.norm_constant_at_unassigned (S.selection n).batch.primeAt
    (fun i => (primes i.val).property) (S.selection n).choice.N
    ((S.selection n).plan.degree - 1 + 1) p.val
  intro i heq
  apply hp
  have hpi : primes i.val = p := Subtype.ext heq
  exact hpi ▸ ((S.selection n).batch.mem_indices i.val).mp i.property

/-- The outside-processing raw primary value follows from actual coefficient
support and the selected signed constant, with no profile hypothesis. -/
theorem primary_residue_zero (p : PrimeIndex) (hp : R.primary.paired p) :
    PadicInt.toZMod (R.primary.value p hp) = 0 := by
  by_contra hz
  exact R.primary.nonunit p hp ((padicInt_isUnit_iff_toZMod_ne_zero _).mpr hz)

theorem raw_primary_norm_unprocessed (n : ℕ) (p : PrimeIndex) (hp : R.primary.paired p)
    (hj : p ∉ (S.selection n).batch.processed.primes) :
    ‖(S.chain.raw n).eval₂ (algebraMap ℚ ℚ_[p.val]) (R.primary.value p hp).val‖ = 1 := by
  apply norm_one_at_unassigned_primary (S.selection n).batch.processed (S.chain.raw n)
    (S.chain.raw_monic n) _ p hj (raw_constant_norm S n _ hj)
    (R.primary.value p hp) (primary_residue_zero (R := R) p hp)
  intro k p hp
  rw [← batch_eq_selection]
  exact S.chain.raw_support n k p hp

theorem generator_primary_norm_unprocessed (n : ℕ) (p : PrimeIndex) (hp : R.primary.paired p)
    (hj : p ∉ (S.selection n).batch.processed.primes) :
    ‖EvaluationDVR.evaluationHom p.val (R.primary.value p hp).val (R.primary.transcendental p hp)
      (generators S n)‖ = 1 := by
  rw [generators_eq_quotient, ReturnTargets.evaluation_normalized_polynomial, norm_div,
    raw_primary_norm_unprocessed S n p hp hj,
    denominator_norm_one S.chain.raw S.chain.exponent n (R.primary.value p hp).val, div_one]
  intro k hk
  exact raw_primary_norm_unprocessed S k p hp (fun hm => hj (earlier_processed_subset S k n hk hm))

theorem order_zero_unprocessed (ht : TargetNorms S order) (n : ℕ) (p : PrimeIndex)
    (hj : p ∉ (S.selection n).batch.processed.primes) : order n p = 0 := by
  by_contra hn
  apply hj
  rw [(S.selection n).progress.processed]
  exact Finset.mem_union_right _ (ht.support n p hn)

/-- Active selected-primary orders are consequences of the actual local selector
and coefficient support, including outside current processing. -/
theorem generator_primary_norm (ht : TargetNorms S order) (n : ℕ) (p : PrimeIndex)
    (hp : R.primary.paired p) :
    ‖EvaluationDVR.evaluationHom p.val (R.primary.value p hp).val (R.primary.transcendental p hp)
      (generators S n)‖ = (p.val : ℝ) ^ (-(order n p : ℤ)) := by
  by_cases hj : p ∈ (S.selection n).batch.processed.primes
  · obtain ⟨j, rfl⟩ := primes.surjective p
    let i : (S.selection n).batch.indices := ⟨j, ((S.selection n).batch.mem_indices j).mpr hj⟩
    have hb : MixedStageSelection.Active (R.primary.paired (primes i.val)) false := Or.inr hp
    have hn := processed_norm S n i false hb
    rw [ht.norm n i false hb] at hn
    have he := evaluationHom_congr ((S.selection n).batch.primeAt i)
      (R.primary.branch_transcendental (S.selection n).batch i false hb)
      (R.primary.transcendental (primes j) hp)
      (R.primary.branch_false (S.selection n).batch i hp)
    rw [he] at hn
    exact hn
  · rw [generator_primary_norm_unprocessed S n p hp hj, order_zero_unprocessed S ht n p hj]
    simp

theorem generator_primary_addValuation (ht : TargetNorms S order) (n : ℕ) (p : PrimeIndex)
    (hp : R.primary.paired p) :
    (EvaluationDVR.evaluationHom p.val (R.primary.value p hp).val (R.primary.transcendental p hp)
      (generators S n)).valuation = order n p := by
  apply ReturnTargets.valuation_of_target_norm (order n p) (0 : ℚ_[p.val])
  rw [generator_primary_norm S ht n p hp, ReturnTargets.quotientTarget_norm]

theorem generator_primary_valuation (ht : TargetNorms S order) (n : ℕ) (p : PrimeIndex)
    (hp : R.primary.paired p) :
    EvaluationDVR.evaluationValuation p.val (R.primary.value p hp).val (R.primary.transcendental p hp)
      (generators S n) = WithZero.exp (-(order n p : ℤ)) := by
  classical
  have hn : EvaluationDVR.evaluationHom p.val (R.primary.value p hp).val (R.primary.transcendental p hp)
      (generators S n) ≠ 0 := by
    apply norm_ne_zero_iff.mp
    rw [generator_primary_norm S ht n p hp]
    exact ne_of_gt (zpow_pos (by exact_mod_cast p.property.pos) _)
  change Padic.mulValuation _ = _
  change (if _ = 0 then 0 else WithZero.exp (-(_ : ℚ_[p.val]).valuation)) = _
  rw [ite_eq_right_iff.mpr (fun hz => False.elim (hn hz)), generator_primary_addValuation S ht n p hp]

end UnconditionalCounterexample.MixedSequenceValuations
