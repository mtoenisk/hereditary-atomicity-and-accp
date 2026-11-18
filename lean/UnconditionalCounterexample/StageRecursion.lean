import UnconditionalCounterexample.RecursivePrefix
import UnconditionalCounterexample.BatchArguments

/-!
# Recursion with the actual polynomial choice at each stage

Beginning with the empty prefix, choose the common raw denominator and degree,
assign the ordinary and auxiliary primes, and select the polynomial on these
arguments. The recursive append uses precisely that polynomial and its chosen
normalization exponent. The whole selection is retained at each stage so its
local estimates, geometric tests, auxiliary model and guard transition can
be applied to the resulting global sequence. The choice of target values for
each specific b- or q-stage is supplied by the requirements.
-/

noncomputable section
namespace UnconditionalCounterexample.StageRecursion

open Polynomial GuardSupport CombinedGuardStep RecursivePrefix ConstructionWords PrimaryChoices

/-- The information carried from prime assignment into the polynomial choice. -/
structure BatchProgress {n : ℕ} (P : Prefix n) (degree : ℕ) (needed : Finset PrimeIndex)
    (B : Batch) : Prop where
  stage : B.stage = n
  processed : B.processed.primes = P.state.assignment.primes ∪
    GuardStages.primesThrough B.cutoff ∪ needed
  old_guard : ∀ p (hp : p ∈ P.state.assignment.primes) (hp' : p ∈ B.assigned.primes),
    B.assigned.guard p hp' = P.state.assignment.guard p hp
  new_guard : ∀ p (hp : p ∈ B.assigned.primes), p ∉ P.state.assignment.primes →
    (B.assigned.guard p hp).birth = n ∧ ∀ j : Fin n,
      ‖(P.raw j).eval₂ (algebraMap ℚ ℚ_[p.val]) (B.assigned.guard p hp).value.val‖ = 1
  cutoff_gt : P.state.cutoff < B.cutoff
  degree_budget : 2 ^ (4 + (∑ j, (P.raw j).natDegree) + degree) ≤ B.cutoff

theorem exists_processing_batch {n : ℕ} (P : Prefix n) (start : n = 0 → P.state = zeroState)
    (degree : ℕ) (needed : Finset PrimeIndex) : ∃ B, BatchProgress P degree needed B := by
  by_cases hn : n = 0
  · subst n
    have hstart := start rfl
    obtain ⟨B, hstage, hcut, hproc, _, hbirth⟩ := exists_initial_batch degree needed
    refine ⟨B, hstage, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [hstart, zeroState] using hproc
    · intro p hp
      simp [hstart, zeroState] at hp
    · exact fun p hp _ => ⟨hbirth p hp, fun j => Fin.elim0 j⟩
    · simp [hstart, zeroState, hcut]
    · simp [hcut]
  · obtain ⟨B, hstage, _, hproc, hcut, hdeg, _, hguard, hnew⟩ :=
      exists_successor_batch P.state P.raw P.monic P.current_support (P.current_degree_budget hn)
        n degree needed
    exact ⟨B, hstage, hproc, hguard, hnew, hcut, hdeg.le⟩

/-- Normalized target values and the requested relative precisions at a batch. -/
structure Targets (B : Batch) where
  value : ∀ i : B.indices, Bool → ℚ_[B.primeAt i]
  precision : B.indices → Bool → ℕ
  nonzero : ∀ i b, value i b ≠ 0

/-- The raw stage specifies its finitely supported primary column before prime
assignment. Its normalized targets may use the earlier polynomials and all
currently assigned arguments. -/
structure Requirements where
  needed : ℕ → Finset PrimeIndex
  targets : ∀ {n}, Prefix n → (B : Batch) → Targets B

/-- Keep both choices as data so all the global consequences refer to the
polynomial that was actually appended. -/
structure Selection (R : Requirements) {n : ℕ} (P : Prefix n) where
  plan : DegreePlan n P.rawAt P.exponentAt
  batch : Batch
  progress : BatchProgress P plan.degree (R.needed n) batch
  choice : Choice batch.primeAt batch.auxiliary.val plan batch.branch
    (R.targets P batch).value (R.targets P batch).precision

theorem selection_nonempty (R : Requirements) {n : ℕ} (P : Prefix n)
    (start : n = 0 → P.state = zeroState) : Nonempty (Selection R P) := by
  obtain ⟨plan⟩ := degreePlan_nonempty n P.rawAt P.exponentAt P.rawAt_monic
  obtain ⟨B, hB⟩ := exists_processing_batch P start plan.degree (R.needed n)
  let t := R.targets P B
  obtain ⟨c⟩ := B.choice_nonempty plan P.rawAt_monic t.value t.precision t.nonzero
  exact ⟨⟨plan, B, hB, c⟩⟩

namespace Selection
variable {R : Requirements} {n : ℕ} {P : Prefix n} (s : Selection R P)

def constant : ℚ := SignedConstant.constant s.batch.primeAt s.choice.N (s.plan.degree - 1 + 1)

def raw : ℚ[X] := ShiftedEisenstein.monicFamily (s.plan.degree - 1) s.constant s.choice.coeff

theorem raw_degree : s.raw.natDegree = s.plan.degree := s.choice.witnesses.2.1

theorem raw_tests : ∀ t ∈ s.plan.tests, t.Holds (s.raw.map (algebraMap ℚ (AlgebraicClosure ℚ))) :=
  s.choice.witnesses.2.2.2.2.2.2.1

def toNext : Next P where
  raw := s.raw
  exponent := s.plan.E
  batch := s.batch
  monic := s.choice.witnesses.1
  irreducible := s.choice.witnesses.2.2.2.1
  constant_ne_zero := by
    rw [show s.raw.coeff 0 = s.constant from s.choice.witnesses.2.2.1]
    exact SignedConstant.constant_ne_zero _ (fun _ => Fact.out) _ _
  degree_five := s.raw_degree ▸ s.plan.large_degree
  exponent_pos := s.plan.E_pos
  degree_gt := by
    intro j
    simpa only [s.raw_degree, Prefix.rawAt_lt P j.val j.isLt] using s.plan.increasing j.val j.isLt
  batch_stage := s.progress.stage
  raw_support := by
    intro k p hp
    obtain ⟨j, heq⟩ := s.choice.witnesses.2.2.2.2.1 k p p.property hp
    have h : p = primes j.val := Subtype.ext heq
    exact h ▸ (s.batch.mem_indices _).mp j.property
  assigned_subset := by
    intro p hp
    apply s.batch.processed_subset_assigned
    rw [s.progress.processed]
    exact Finset.mem_union_left _ (Finset.mem_union_left _ hp)
  guard_persistent := s.progress.old_guard
  new_birth := fun p hp hm => (s.progress.new_guard p hp hm).1
  cutoff_gt := s.progress.cutoff_gt
  stage_cutoff := Nat.succ_le_of_lt (P.stage_cutoff.trans_lt s.progress.cutoff_gt)
  degree_budget := by rw [s.raw_degree]; exact s.progress.degree_budget

end Selection

/-- A coherent family keeps every finite-stage witness, in addition to the
structural prefix chain. -/
structure Sequence (R : Requirements) where
  chain : Chain
  selection : ∀ n, Selection R (chain.approx n)
  consistent : ∀ n, chain.next n = (selection n).toNext

private def stage (R : Requirements) {n : ℕ} (P : Prefix n)
    (h : n = 0 → P.state = zeroState) : Selection R P :=
  Classical.choice (selection_nonempty R P h)

private def build (R : Requirements) : (n : ℕ) → {P : Prefix n // n = 0 → P.state = zeroState}
  | 0 => ⟨empty, fun _ => rfl⟩
  | n + 1 => ⟨(stage R (build R n).val (build R n).property).toNext.append, by omega⟩

def sequence (R : Requirements) : Sequence R where
  chain := {
    approx := fun n => (build R n).val
    next := fun n => (stage R (build R n).val (build R n).property).toNext
    initial := rfl
    step := fun _ => rfl }
  selection := fun n => stage R (build R n).val (build R n).property
  consistent := fun _ => rfl

end UnconditionalCounterexample.StageRecursion
