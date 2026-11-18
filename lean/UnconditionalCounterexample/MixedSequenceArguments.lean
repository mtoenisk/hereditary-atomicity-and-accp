import UnconditionalCounterexample.MixedGlobalPlans
import UnconditionalCounterexample.ReturnChain
import UnconditionalCounterexample.RawEvaluationPromises

/-!
# Permanent arguments and processing for the mixed sequence

The branch used by each actual finite selection is the same permanent guard
or fixed selected primary used by the global sequence. Every fixed prime is
eventually processed, and requested support primes are processed immediately.
Transcendence, integrality and denominator nonvanishing are asserted only for
active branches; an unselected false array entry imposes no condition.
-/

noncomputable section
namespace UnconditionalCounterexample.MixedSequenceArguments

open Polynomial Filter PrimaryChoices CombinedGuardStep ConstructionWords
  MixedStageRecursion RawEvaluationPromises

variable {R : Requirements}

/-- Actual permanent branch data; the false entry is unused when unpaired. -/
def branch (seq : Sequence R) (j : ℕ) (b : Bool) : ℚ_[(primes j).val] :=
  by
    classical
    exact if b then (seq.chain.guardChain.value (primes j)).val
      else if hp : R.primary.paired (primes j) then (R.primary.value (primes j) hp).val else 0

theorem sequence_batch_eq_selection (seq : Sequence R) (n : ℕ) :
    seq.chain.batch n = (seq.selection n).batch := by
  rw [seq.chain.batch_eq_selected, seq.consistent]
  rfl

theorem selection_mem_indices (seq : Sequence R) (n j : ℕ)
    (hj : (primes j).val ≤ n + 1) : j ∈ (seq.selection n).batch.indices := by
  apply ((seq.selection n).batch.mem_indices j).mpr
  apply (seq.selection n).batch.covered
  apply (GuardStages.mem_primesThrough _ _).mpr
  exact hj.trans (seq.selection n).toNext.stage_cutoff

theorem assignment_eq_selection (seq : Sequence R) (n : ℕ) :
    seq.chain.guardChain.assignments n = (seq.selection n).batch.assigned := by
  rw [seq.chain.guardChain_assignments, sequence_batch_eq_selection]

/-- A processed guard is the actual permanent guard of the same sequence. -/
theorem selection_guard_eq (seq : Sequence R) (n : ℕ)
    (j : (seq.selection n).batch.indices) :
    ((seq.selection n).batch.guardAt j).value = seq.chain.guardChain.value (primes j.val) := by
  have hguard : ∀ hp : primes j.val ∈ (seq.selection n).batch.assigned.primes,
      ((seq.selection n).batch.assigned.guard (primes j.val) hp).value =
        seq.chain.guardChain.value (primes j.val) := by
    have hv := seq.chain.guardChain.value_agrees n (primes j.val)
    simpa only [assignment_eq_selection] using hv
  have hp := ((seq.selection n).batch.mem_indices j.val).mp j.property
  have he := hguard ((seq.selection n).batch.processed_subset_assigned hp)
  rw [(seq.selection n).batch.assigned_old (primes j.val) hp] at he
  exact he

theorem selection_branch_eq (seq : Sequence R) (n : ℕ)
    (j : (seq.selection n).batch.indices) (b : Bool) :
    R.primary.branch (seq.selection n).batch j b = branch seq j.val b := by
  cases b with
  | false => rfl
  | true => exact congrArg Subtype.val (selection_guard_eq seq n j)

/-- Every sufficiently small rational prime is already processed at this stage. -/
theorem processed_of_le (seq : Sequence R) (n : ℕ) (p : GuardSupport.PrimeIndex)
    (hp : p.val ≤ n + 1) : p ∈ (seq.selection n).batch.processed.primes := by
  apply (seq.selection n).batch.covered
  apply (GuardStages.mem_primesThrough _ _).mpr
  exact hp.trans (seq.selection n).toNext.stage_cutoff

/-- Every explicitly requested primary-support prime is processed immediately. -/
theorem needed_subset_processed (seq : Sequence R) (n : ℕ) :
    R.needed n ⊆ (seq.selection n).batch.processed.primes := by
  rw [(seq.selection n).progress.processed]
  exact Finset.subset_union_right

theorem selection_mem_indices_of_needed (seq : Sequence R) (n j : ℕ)
    (hj : primes j ∈ R.needed n) : j ∈ (seq.selection n).batch.indices :=
  ((seq.selection n).batch.mem_indices j).mpr (needed_subset_processed seq n hj)

/-- Every fixed prime occurs in all sufficiently late ordinary processing sets. -/
theorem eventually_mem_indices (seq : Sequence R) (j : ℕ) :
    ∀ᶠ n in atTop, j ∈ (seq.selection n).batch.indices := by
  filter_upwards [eventually_ge_atTop (primes j).val] with n hn
  exact selection_mem_indices seq n j (hn.trans (Nat.le_succ n))




theorem eventually_processed (seq : Sequence R) (p : GuardSupport.PrimeIndex) :
    ∀ᶠ n in atTop, p ∈ (seq.selection n).batch.processed.primes := by
  filter_upwards [eventually_ge_atTop p.val] with n hn
  exact processed_of_le seq n p (hn.trans (Nat.le_succ n))

@[simp] theorem branch_true (seq : Sequence R) (j : ℕ) :
    branch seq j true = (seq.chain.guardChain.value (primes j)).val := rfl

@[simp] theorem branch_false (seq : Sequence R) (j : ℕ)
    (hp : R.primary.paired (primes j)) :
    branch seq j false = (R.primary.value (primes j) hp).val := by
  simp only [branch, Bool.false_eq_true, ↓reduceIte, hp, ↓reduceDIte]

theorem branch_transcendental (seq : Sequence R) (j : ℕ) (b : Bool)
    (hb : MixedStageSelection.Active (R.primary.paired (primes j)) b) :
    Transcendental ℚ (branch seq j b) := by
  cases b with
  | true => exact seq.chain.guardChain.value_transcendental (primes j)
  | false =>
    have hp : R.primary.paired (primes j) := hb.resolve_left (by decide)
    rw [branch_false seq j hp]
    exact R.primary.transcendental _ hp

theorem branch_integral (seq : Sequence R) (j : ℕ) (b : Bool)
    (hb : MixedStageSelection.Active (R.primary.paired (primes j)) b) :
    branch seq j b ∈ PadicInt.subring (primes j).val := by
  cases b with
  | true => exact (seq.chain.guardChain.value (primes j)).property
  | false =>
    have hp : R.primary.paired (primes j) := hb.resolve_left (by decide)
    rw [branch_false seq j hp]
    exact (R.primary.value _ hp).property

theorem branch_ne (seq : Sequence R) (j : ℕ) (hp : R.primary.paired (primes j)) :
    branch seq j false ≠ branch seq j true := by
  rw [branch_false seq j hp, branch_true]
  intro heq
  have heq' : R.primary.value (primes j) hp = seq.chain.guardChain.value (primes j) := Subtype.ext heq
  exact R.primary.nonunit _ hp (heq'.symm ▸ seq.chain.guardChain.value_unit (primes j))

theorem raw_eval_ne_zero (seq : Sequence R) (n j : ℕ) (b : Bool)
    (hb : MixedStageSelection.Active (R.primary.paired (primes j)) b) :
    (seq.chain.raw n).eval₂ (algebraMap ℚ ℚ_[(primes j).val]) (branch seq j b) ≠ 0 := by
  intro h
  exact (seq.chain.raw_monic n).ne_zero ((transcendental_iff.mp
    (branch_transcendental seq j b hb)) (seq.chain.raw n) h)

theorem global_wordDen_eval_ne_zero (seq : Sequence R) (n : ℕ) (w : Word n)
    (j : ℕ) (b : Bool) (hb : MixedStageSelection.Active (R.primary.paired (primes j)) b) :
    ((MixedGlobalPlans.globalPlan seq n).wordDen w).eval₂
      (algebraMap ℚ ℚ_[(primes j).val]) (branch seq j b) ≠ 0 := by
  rw [← eval_map]
  exact old_product_eval_ne_zero_of_transcendental n seq.chain.raw
    (fun k _ => seq.chain.raw_monic k) ((MixedGlobalPlans.globalPlan seq n).powers w)
    (branch seq j b) (branch_transcendental seq j b hb)

end UnconditionalCounterexample.MixedSequenceArguments
