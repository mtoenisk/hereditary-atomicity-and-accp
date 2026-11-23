import UnconditionalCounterexample.MixedGlobalPlans
import UnconditionalCounterexample.MixedWordTransfer

/-!
# Prefix-dependent choices of primary primes

The ordinary processing batch and the shifted-Eisenstein auxiliary prime are chosen
after the degree and preceding polynomials are known. At the first assignment of
a prime the prescription can give its permanent guard a primary in a distinct
residue class. The entire fibre is copied at every subsequent stage, including
when its first assignment was as the auxiliary prime.
-/

noncomputable section
namespace UnconditionalCounterexample.Variations.Univariate

open Polynomial Filter GuardSupport PrimaryChoices CombinedGuardStep RecursivePrefix ConstructionWords

/-- The primary may itself be a unit. Distinct residues provide both interpolation
points and the integral determinant needed for conductor lifting. -/
abbrev Primary (p : PrimeIndex) (guard : ℤ_[p.val]) :=
  {a : ℤ_[p.val] // Transcendental ℚ a.val ∧ PadicInt.toZMod a ≠ PadicInt.toZMod guard}

structure Site (p : PrimeIndex) where
  guard : ℤ_[p.val]
  guard_trans : Transcendental ℚ guard.val
  primary : Option (Primary p guard)

namespace Site
variable {p : PrimeIndex} (s : Site p)

def paired : Prop := s.primary.isSome = true

def branch : Bool → ℚ_[p.val]
  | true => s.guard.val
  | false => (s.primary.map (fun a => a.val.val)).getD 0

theorem branch_transcendental (b : Bool) (hb : MixedStageSelection.Active s.paired b) :
    Transcendental ℚ (s.branch b) := by
  cases b with
  | true => exact s.guard_trans
  | false =>
    obtain h := hb.resolve_left (by decide)
    cases he : s.primary with
    | none => simp [paired, he] at h
    | some a => simpa [branch, he] using a.property.1

theorem branch_integral (b : Bool) : s.branch b ∈ PadicInt.subring p.val := by
  cases b with
  | true => exact s.guard.property
  | false =>
    cases he : s.primary with
    | none => simp [branch, he]
    | some a => simpa [branch, he] using a.val.property

theorem difference_isUnit (a : Primary p s.guard) : IsUnit (s.guard - a.val) := by
  apply (padicInt_isUnit_iff_toZMod_ne_zero _).mpr
  rw [map_sub]
  exact sub_ne_zero.mpr a.property.2.symm

theorem branch_ne (hp : s.paired) : s.branch false ≠ s.branch true := by
  cases he : s.primary with
  | none => simp [paired, he] at hp
  | some a =>
    intro h
    have hf : a.val.val = s.guard.val := by simpa [branch, he] using h
    exact a.property.2 (congrArg PadicInt.toZMod (Subtype.ext hf : a.val = s.guard))

end Site

abbrev Table (primes : Finset PrimeIndex) := (p : PrimeIndex) → p ∈ primes → Site p

/-- Read a site from the batch's permanent assignment at an ordinary processed prime. -/
def siteAt (B : Batch) (sites : Table B.assigned.primes) (j : B.indices) : Site (primes j.val) :=
  sites _ (B.processed_subset_assigned ((B.mem_indices _).mp j.property))

structure Targets (B : Batch) (sites : Table B.assigned.primes) where
  value : ∀ j : B.indices, Bool → ℚ_[B.primeAt j]
  precision : B.indices → Bool → ℕ
  nonzero : ∀ j b, MixedStageSelection.Active (siteAt B sites j).paired b → value j b ≠ 0

/-- Requests and target values can inspect the prefix and every prior role.
The prime allocation is made before the numerator is selected. -/
structure Requirements where
  degreeFloor : ∀ {n} (P : Prefix n), Table P.state.assignment.primes → ℕ := fun _ _ => 0
  needed : ∀ {n} (P : Prefix n), Table P.state.assignment.primes → Finset PrimeIndex
  chooseBatch : ∀ {n} (P : Prefix n) (old : Table P.state.assignment.primes),
    (n = 0 → P.state = zeroState) → (d : ℕ) →
    {B : Batch // StageRecursion.BatchProgress P d (needed P old) B} :=
    fun P old start d =>
      ⟨(StageRecursion.exists_processing_batch P start d (needed P old)).choose,
        (StageRecursion.exists_processing_batch P start d (needed P old)).choose_spec⟩
  newPrimary : ∀ {n} (P : Prefix n), Table P.state.assignment.primes →
    (B : Batch) → (p : PrimeIndex) → (hp : p ∈ B.assigned.primes) →
    p ∉ P.state.assignment.primes → Option (Primary p (B.assigned.guard p hp).value)
  targets : ∀ {n} (P : Prefix n), Table P.state.assignment.primes →
    (B : Batch) → (sites : Table B.assigned.primes) → Targets B sites

/-- Allocate a fibre once, carrying the old site itself at every subsequent stage. -/
def extend (R : Requirements) {n} (P : Prefix n) (old : Table P.state.assignment.primes)
    (B : Batch) : Table B.assigned.primes := by
  classical
  intro p hp
  exact if h : p ∈ P.state.assignment.primes then old p h
    else ⟨(B.assigned.guard p hp).value, (B.assigned.guard p hp).transcendental,
      R.newPrimary P old B p hp h⟩

theorem extend_old (R : Requirements) {n} (P : Prefix n) (old : Table P.state.assignment.primes)
    (B : Batch) (p : PrimeIndex) (hp : p ∈ B.assigned.primes)
    (h : p ∈ P.state.assignment.primes) : extend R P old B p hp = old p h := by
  simp [extend, h]

structure Selection (R : Requirements) {n} (P : Prefix n) (old : Table P.state.assignment.primes) where
  plan : DegreePlan n P.rawAt P.exponentAt
  degree_above : R.degreeFloor P old < plan.degree
  batch : Batch
  progress : StageRecursion.BatchProgress P plan.degree (R.needed P old) batch
  batch_used : ∀ start, batch = (R.chooseBatch P old start plan.degree).val
  choice : let sites := extend R P old batch
    let targets := R.targets P old batch sites
    MixedConstructionWords.Choice batch.primeAt (fun j => (siteAt batch sites j).paired)
      batch.auxiliary.val plan (fun j => (siteAt batch sites j).branch)
      targets.value targets.precision

theorem selection_nonempty (R : Requirements) {n} (P : Prefix n)
    (old : Table P.state.assignment.primes) (start : n = 0 → P.state = zeroState) :
    Nonempty (Selection R P old) := by
  obtain ⟨basePlan⟩ := degreePlan_nonempty n P.rawAt P.exponentAt P.rawAt_monic
  let d := max basePlan.degree (R.degreeFloor P old + 1)
  have hd : basePlan.degree ≤ d := le_max_left _ _
  let plan : DegreePlan n P.rawAt P.exponentAt :=
    { basePlan with
      degree := d
      large_degree := basePlan.large_degree.trans hd
      increasing := fun j hj => (basePlan.increasing j hj).trans_le hd
      infinity := fun w => (basePlan.infinity w).trans_le (Nat.mul_le_mul_left _ hd) }
  have hfloor : R.degreeFloor P old < plan.degree :=
    Nat.lt_of_succ_le (le_max_right basePlan.degree (R.degreeFloor P old + 1))
  let B := (R.chooseBatch P old start plan.degree).val
  let sites := extend R P old B
  let t := R.targets P old B sites
  obtain ⟨c⟩ := MixedConstructionWords.choice_nonempty B.primeAt
    (fun j => (siteAt B sites j).paired) B.auxiliary.val plan
    (fun j => (siteAt B sites j).branch) t.value t.precision
    (Subtype.val_injective.comp (primes.injective.comp Subtype.val_injective))
    (fun i h => B.auxiliary_fresh ((show primes i.val = B.auxiliary from Subtype.ext h) ▸
      (B.mem_indices _).mp i.property))
    P.rawAt_monic (fun i => (siteAt B sites i).branch_transcendental)
    (fun i => (siteAt B sites i).branch_ne) t.nonzero
  exact ⟨⟨plan, hfloor, B, (R.chooseBatch P old start plan.degree).property, fun _ => rfl, c⟩⟩

namespace Selection
variable {R : Requirements} {n : ℕ} {P : Prefix n} {old : Table P.state.assignment.primes}
  (s : Selection R P old)

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

private structure State (n : ℕ) where
  prefixData : Prefix n
  old : Table prefixData.state.assignment.primes
  start : n = 0 → prefixData.state = zeroState

private def step (R : Requirements) {n} (state : State n) :=
  Classical.choice (selection_nonempty R state.prefixData state.old state.start)

private def build (R : Requirements) : (n : ℕ) → State n
  | 0 => ⟨empty, fun p hp => False.elim ((Finset.notMem_empty p) hp), fun _ => rfl⟩
  | n + 1 =>
    let st := build R n
    let s := step R st
    ⟨s.toNext.append, extend R st.prefixData st.old s.batch, by omega⟩

/-- The actual polynomial and role sequence attached to a prescription. -/
def chain (R : Requirements) : Chain where
  approx n := (build R n).prefixData
  next n := (step R (build R n)).toNext
  initial := rfl
  step _ := rfl

def table (R : Requirements) (n : ℕ) : Table ((chain R).approx n).state.assignment.primes :=
  (build R n).old

def selection (R : Requirements) (n : ℕ) : Selection R ((chain R).approx n) (table R n) :=
  step R (build R n)

theorem table_persistent (R : Requirements) (n : ℕ) (p : PrimeIndex)
    (h : p ∈ ((chain R).approx n).state.assignment.primes)
    (h' : p ∈ ((chain R).approx (n+1)).state.assignment.primes) :
    table R (n+1) p h' = table R n p h :=
  extend_old R _ (table R n) (selection R n).batch p h' h

end UnconditionalCounterexample.Variations.Univariate
