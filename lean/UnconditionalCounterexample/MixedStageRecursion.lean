import UnconditionalCounterexample.StageRecursion
import UnconditionalCounterexample.MixedConstructionWords

/-!
# Recursion with actual mixed local selections

Fixed primary arguments are supplied only at the selected rational primes.
Every batch uses its actual permanent guard assignment. The mixed selector
chooses the raw polynomial for this prefix and appends exactly that polynomial,
normalization power and batch through the existing structural Prefix/Next API.
No polynomial-selection or recursive-existence premise is assumed.
-/

noncomputable section
namespace UnconditionalCounterexample.MixedStageRecursion

open Polynomial GuardSupport CombinedGuardStep RecursivePrefix ConstructionWords PrimaryChoices

/-- Fixed selected primary arguments. The actual batch guard is always
provided by the existing permanent guard assignment, independently of this data. -/
structure PrimaryData where
  paired : PrimeIndex → Prop
  value : ∀ p, paired p → ℤ_[p.val]
  transcendental : ∀ p hp, Transcendental ℚ (value p hp).val
  nonunit : ∀ p hp, ¬ IsUnit (value p hp)

namespace PrimaryData

/-- The unused false entry is zero. All mathematical requirements are restricted
to active branches, so it imposes no condition at an unselected prime. -/
def branch (d : PrimaryData) (B : Batch) (i : B.indices) (b : Bool) : ℚ_[B.primeAt i] := by
  classical
  exact if b then (B.guardAt i).value.val
    else if hp : d.paired (primes i.val) then (d.value (primes i.val) hp).val else 0

@[simp] theorem branch_true (d : PrimaryData) (B : Batch) (i : B.indices) :
    d.branch B i true = (B.guardAt i).value.val := by
  rfl

@[simp] theorem branch_false (d : PrimaryData) (B : Batch) (i : B.indices)
    (hp : d.paired (primes i.val)) :
    d.branch B i false = (d.value (primes i.val) hp).val := by
  simp only [branch, Bool.false_eq_true, ↓reduceIte, hp, ↓reduceDIte]
  rfl

theorem branch_transcendental (d : PrimaryData) (B : Batch) (i : B.indices)
    (b : Bool) (hb : MixedStageSelection.Active (d.paired (primes i.val)) b) :
    Transcendental ℚ (d.branch B i b) := by
  cases b with
  | true => exact (B.guardAt i).transcendental
  | false =>
    have hp : d.paired (primes i.val) := hb.resolve_left (by decide)
    rw [branch_false d B i hp]
    exact d.transcendental _ hp

theorem branch_ne (d : PrimaryData) (B : Batch) (i : B.indices)
    (hp : d.paired (primes i.val)) : d.branch B i false ≠ d.branch B i true := by
  rw [branch_false d B i hp, branch_true]
  intro heq
  have heq' : d.value (primes i.val) hp = (B.guardAt i).value := Subtype.ext heq
  exact d.nonunit _ hp (heq'.symm ▸ (B.guardAt i).unit)

theorem choice_nonempty (d : PrimaryData) (B : Batch)
    {n : ℕ} {P : ℕ → ℚ[X]} {oldE : ℕ → ℕ}
    (plan : DegreePlan n P oldE) (hP : ∀ j < n, (P j).Monic)
    (v : ∀ i : B.indices, Bool → ℚ_[B.primeAt i]) (kv : B.indices → Bool → ℕ)
    (hv : ∀ i b, MixedStageSelection.Active (d.paired (primes i.val)) b → v i b ≠ 0) :
    Nonempty (MixedConstructionWords.Choice B.primeAt
      (fun i => d.paired (primes i.val)) B.auxiliary.val plan (d.branch B) v kv) := by
  apply MixedConstructionWords.choice_nonempty _ _ _ _ _ _ _ _ _ hP
    (d.branch_transcendental B) (d.branch_ne B) hv
  · exact Subtype.val_injective.comp (primes.injective.comp Subtype.val_injective)
  · intro i h
    apply B.auxiliary_fresh
    have heq : primes i.val = B.auxiliary := Subtype.ext h
    exact heq ▸ (B.mem_indices _).mp i.property

end PrimaryData

/-- Normalized target values and the requested relative precisions at a batch. -/
structure Targets (d : PrimaryData) (B : Batch) where
  value : ∀ i : B.indices, Bool → ℚ_[B.primeAt i]
  precision : B.indices → Bool → ℕ
  nonzero : ∀ i b, MixedStageSelection.Active (d.paired (primes i.val)) b → value i b ≠ 0

/-- The raw stage specifies its finitely supported primary column before prime
assignment. Its normalized targets may use the earlier polynomials and all
currently assigned arguments. -/
structure Requirements where
  primary : PrimaryData
  needed : ℕ → Finset PrimeIndex
  targets : ∀ {n}, Prefix n → (B : Batch) → Targets primary B

/-- Keep both choices as data so all the global consequences refer to the
polynomial that was actually appended. -/
structure Selection (R : Requirements) {n : ℕ} (P : Prefix n) where
  plan : DegreePlan n P.rawAt P.exponentAt
  batch : Batch
  progress : StageRecursion.BatchProgress P plan.degree (R.needed n) batch
  choice : MixedConstructionWords.Choice batch.primeAt
    (fun i => R.primary.paired (primes i.val)) batch.auxiliary.val plan (R.primary.branch batch)
    (R.targets P batch).value (R.targets P batch).precision

theorem selection_nonempty (R : Requirements) {n : ℕ} (P : Prefix n)
    (start : n = 0 → P.state = zeroState) : Nonempty (Selection R P) := by
  obtain ⟨plan⟩ := degreePlan_nonempty n P.rawAt P.exponentAt P.rawAt_monic
  obtain ⟨B, hB⟩ := StageRecursion.exists_processing_batch P start plan.degree (R.needed n)
  let t := R.targets P B
  obtain ⟨c⟩ := R.primary.choice_nonempty B plan P.rawAt_monic t.value t.precision t.nonzero
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

end UnconditionalCounterexample.MixedStageRecursion
