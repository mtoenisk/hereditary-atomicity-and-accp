import UnconditionalCounterexample.Variations.UnivariateTransfer

/-!
# Freezing prescribed fresh sites in the polynomial recursion

At a prefix, the application may choose finitely many fresh primes together
with their guards and optional primaries. The realized polynomial batch uses
exactly these sites at the requested primes. Other newly assigned primes are
guard-only, including the fresh Eisenstein prime.
-/

noncomputable section
namespace UnconditionalCounterexample.Variations.Univariate

open Polynomial GuardSupport PrimaryChoices CombinedGuardStep RecursivePrefix ConstructionWords
open PaperGuardStages

/-- A finite family of fresh fibres chosen after inspecting the preceding raws.
The ordinary guard bounds must hold at each requested prime. -/
structure Births {n : ℕ} (P : Prefix n) where
  primes : Finset PrimeIndex
  fresh : ∀ p ∈ primes, p ∉ P.state.assignment.primes
  guard : ∀ p ∈ primes, Guard p
  birth_eq : ∀ p (hp : p ∈ primes), (guard p hp).birth = n
  old_units : ∀ p (hp : p ∈ primes) (j : Fin n),
    ‖(P.raw j).eval₂ (algebraMap ℚ ℚ_[p.val]) (guard p hp).value.val‖ = 1
  primary : ∀ p (hp : p ∈ primes), Option (Primary p (guard p hp).value)

namespace Births
variable {n : ℕ} {P : Prefix n} (a : Births P)

/-- One new coordinate and its selected guard. -/
def singleton (P : Prefix n) (p : PrimeIndex) (hfresh : p ∉ P.state.assignment.primes)
    (g : Guard p) (hbirth : g.birth = n)
    (hunit : ∀ j : Fin n, ‖(P.raw j).eval₂ (algebraMap ℚ ℚ_[p.val]) g.value.val‖ = 1)
    (v : Option (Primary p g.value)) : Births P where
  primes := {p}
  fresh q hq := (Finset.mem_singleton.mp hq) ▸ hfresh
  guard q hq := (Finset.mem_singleton.mp hq).symm ▸ g
  birth_eq q hq := by obtain rfl := Finset.mem_singleton.mp hq; exact hbirth
  old_units q hq := by obtain rfl := Finset.mem_singleton.mp hq; exact hunit
  primary q hq := by obtain rfl := Finset.mem_singleton.mp hq; exact v

def site (p : PrimeIndex) (hp : p ∈ a.primes) : Site p :=
  ⟨(a.guard p hp).value, (a.guard p hp).transcendental, a.primary p hp⟩

/-- Replace only the guards requested at this stage. Finite support and
the auxiliary prime are literally those of the base processing batch. -/
def batch (B : Batch) : Batch := by
  classical
  exact { B with processed := {
    primes := B.processed.primes
    guard := fun p hp => if h : p ∈ a.primes then a.guard p h else B.processed.guard p hp } }

theorem processed_guard (B : Batch) (p : PrimeIndex) (hp : p ∈ B.processed.primes)
    (h : p ∈ a.primes) : ((a.batch B).processed.guard p hp) = a.guard p h := by
  simp [batch, h]

theorem requested_guard {B : Batch} {d : ℕ}
    (hB : StageRecursion.BatchProgress P d a.primes B) (p : PrimeIndex) (h : p ∈ a.primes)
    (hp : p ∈ (a.batch B).assigned.primes) : (a.batch B).assigned.guard p hp = a.guard p h := by
  have hproc : p ∈ (a.batch B).processed.primes := by
    change p ∈ B.processed.primes
    rw [hB.processed]
    exact Finset.mem_union_right _ h
  rw [(a.batch B).assigned_old p hproc]
  exact a.processed_guard B p hproc h

theorem other_guard (B : Batch) (p : PrimeIndex) (h : p ∉ a.primes)
    (hp : p ∈ B.assigned.primes) : (a.batch B).assigned.guard p hp = B.assigned.guard p hp := by
  classical
  rcases Finset.mem_insert.mp hp with he | hproc
  · subst p
    change (a.batch B).assigned.guard (a.batch B).auxiliary _ = B.assigned.guard B.auxiliary _
    rw [(a.batch B).assigned_auxiliary, B.assigned_auxiliary]
    rfl
  · rw [(a.batch B).assigned_old p hproc, B.assigned_old p hproc]
    simp [batch, h]

theorem progress {B : Batch} {d : ℕ} (hB : StageRecursion.BatchProgress P d a.primes B) :
    StageRecursion.BatchProgress P d a.primes (a.batch B) where
  stage := hB.stage
  processed := hB.processed
  old_guard p hp hp' := by
    have h : p ∉ a.primes := fun h => a.fresh p h hp
    exact (a.other_guard B p h hp').trans (hB.old_guard p hp hp')
  new_guard p hp hnew := by
    by_cases h : p ∈ a.primes
    · rw [a.requested_guard hB p h hp]
      exact ⟨a.birth_eq p h, a.old_units p h⟩
    · rw [a.other_guard B p h hp]
      exact hB.new_guard p hp hnew
  cutoff_gt := hB.cutoff_gt
  degree_budget := hB.degree_budget

/-- Transport a freshly requested primary to the chosen batch guard. It is
absent at every unrequested prime. -/
def primaryAt (B : Batch) (p : PrimeIndex) (hp : p ∈ B.assigned.primes) :
    Option (Primary p (B.assigned.guard p hp).value) := by
  classical
  exact if h : p ∈ a.primes then
    if hg : (a.guard p h).value = (B.assigned.guard p hp).value then hg ▸ a.primary p h else none
    else none

theorem site_eq_requested (B : Batch) (p : PrimeIndex) (h : p ∈ a.primes)
    (hp : p ∈ B.assigned.primes) (hg : B.assigned.guard p hp = a.guard p h) :
    (⟨(B.assigned.guard p hp).value, (B.assigned.guard p hp).transcendental, a.primaryAt B p hp⟩ :
      Site p) = a.site p h := by
  unfold primaryAt site
  simp only [h, ↓reduceDIte]
  generalize (B.assigned.guard p hp) = g at *
  subst g
  simp

end Births

/-- Ingredients decided by the application: the finite list of new sites,
the ordinary processing batch (including its remaining guards), and targets. -/
structure Schedule where
  degreeFloor : ∀ {n} (P : Prefix n), Table P.state.assignment.primes → ℕ := fun _ _ => 0
  births : ∀ {n} (P : Prefix n), Table P.state.assignment.primes → Births P
  base : ∀ {n} (P : Prefix n) (_start : n = 0 → P.state = zeroState) (d : ℕ)
    (needed : Finset PrimeIndex), {B : Batch // StageRecursion.BatchProgress P d needed B} :=
    fun P start d needed => ⟨(StageRecursion.exists_processing_batch P start d needed).choose,
      (StageRecursion.exists_processing_batch P start d needed).choose_spec⟩
  targets : ∀ {n} (P : Prefix n), Table P.state.assignment.primes →
    (B : Batch) → (sites : Table B.assigned.primes) → Targets B sites

namespace Schedule
variable (S : Schedule)

def requirements : Requirements where
  degreeFloor := S.degreeFloor
  needed P old := (S.births P old).primes
  chooseBatch P old start d :=
    let a := S.births P old
    let b := S.base P start d a.primes
    ⟨a.batch b.val, a.progress b.property⟩
  newPrimary P old B p hp _ := (S.births P old).primaryAt B p hp
  targets := S.targets

abbrev chosen (n : ℕ) := S.births ((chain S.requirements).approx n) (table S.requirements n)

theorem requested_processed (n : ℕ) {p : PrimeIndex} (hp : p ∈ (S.chosen n).primes) :
    p ∈ (selection S.requirements n).batch.processed.primes := by
  rw [(selection S.requirements n).progress.processed]
  exact Finset.mem_union_right _ hp

/-- All choices, including the primary and the residue of the guard, survive
from the assigned stage into the actual infinite evaluation intersection. -/
theorem permanentSite_requested (n : ℕ) (p : PrimeIndex) (h : p ∈ (S.chosen n).primes) :
    permanentSite S.requirements p = (S.chosen n).site p h := by
  let R := S.requirements
  let P := (chain R).approx n
  let sel := selection R n
  let a := S.chosen n
  have start : n = 0 → P.state = zeroState := by rintro rfl; rfl
  let b := S.base P start sel.plan.degree a.primes
  have hb : sel.batch = a.batch b.val := sel.batch_used start
  have hp : p ∈ sel.batch.assigned.primes := sel.batch.processed_subset_assigned (S.requested_processed n h)
  have hg : sel.batch.assigned.guard p hp = a.guard p h := by
    revert hp
    rw [hb]
    exact fun hp => a.requested_guard b.property p h hp
  have hn : p ∉ P.state.assignment.primes := a.fresh p h
  rw [← table_eq_permanentSite R (n+1) p hp]
  change extend R P (table R n) sel.batch p hp = _
  simp only [extend, hn, ↓reduceDIte]
  exact a.site_eq_requested sel.batch p h hp hg

/-- At its first assignment an unrequested prime becomes guard-only. Its guard
comes from the base batch, and the auxiliary prime is covered by the same rule. -/
theorem permanentSite_other (n : ℕ) (p : PrimeIndex)
    (hfresh : p ∉ ((chain S.requirements).approx n).state.assignment.primes)
    (hother : p ∉ (S.chosen n).primes)
    (hp : p ∈ (selection S.requirements n).batch.assigned.primes) :
    (permanentSite S.requirements p).primary = none ∧
      ∀ start, ∀ hbase : p ∈ (S.base ((chain S.requirements).approx n) start
        (selection S.requirements n).plan.degree (S.chosen n).primes).val.assigned.primes,
      (permanentSite S.requirements p).guard =
        ((S.base ((chain S.requirements).approx n) start
          (selection S.requirements n).plan.degree (S.chosen n).primes).val.assigned.guard p hbase).value := by
  let R := S.requirements
  let P := (chain R).approx n
  let sel := selection R n
  let a := S.chosen n
  have he : permanentSite R p = extend R P (table R n) sel.batch p hp :=
    (table_eq_permanentSite R (n+1) p hp).symm
  change p ∉ P.state.assignment.primes at hfresh
  have hsite : permanentSite R p =
      ⟨(sel.batch.assigned.guard p hp).value, (sel.batch.assigned.guard p hp).transcendental,
        R.newPrimary P (table R n) sel.batch p hp hfresh⟩ := he.trans (dite_eq_right hfresh)
  rw [hsite]
  clear hsite he
  constructor
  · change a.primaryAt sel.batch p hp = none
    exact dite_eq_right hother
  · intro start hbase
    let b := S.base P start sel.plan.degree a.primes
    have hb : sel.batch = a.batch b.val := sel.batch_used start
    change (sel.batch.assigned.guard p hp).value = (b.val.assigned.guard p hbase).value
    revert hp
    rw [hb]
    exact fun hp => congrArg Guard.value (a.other_guard b.val p hother hp)

theorem requested_unique {m n : ℕ} {p : PrimeIndex}
    (hm : p ∈ (S.chosen m).primes) (hn : p ∈ (S.chosen n).primes) : m = n := by
  have f {i j : ℕ} (hi : p ∈ (S.chosen i).primes) (hj : p ∈ (S.chosen j).primes) :
      ¬ i < j := by
    intro h
    exact (S.chosen j).fresh p hj (assigned_mono S.requirements h
      ((selection S.requirements i).batch.processed_subset_assigned (S.requested_processed i hi)))
  exact le_antisymm (Nat.le_of_not_gt (f hn hm)) (Nat.le_of_not_gt (f hm hn))

/-- Every global primary arose from one requested site; conversely every
requested paired site remains paired permanently. -/
theorem permanent_paired_iff (p : PrimeIndex) : (permanentSite S.requirements p).paired ↔
    ∃ n, ∃ h : p ∈ (S.chosen n).primes, ((S.chosen n).site p h).paired := by
  constructor
  · intro hpair
    let C := (chain S.requirements).guardChain
    let n := C.birth p
    have hp : p ∈ (selection S.requirements n).batch.assigned.primes := C.birth_mem p
    have hfresh : p ∉ ((chain S.requirements).approx n).state.assignment.primes := by
      cases hn : n with
      | zero => exact Finset.notMem_empty p
      | succ m =>
        intro hm
        exact C.not_mem_before_birth p (n := m) (by change m < n; omega) hm
    by_cases h : p ∈ (S.chosen n).primes
    · exact ⟨n, h, S.permanentSite_requested n p h ▸ hpair⟩
    · have hnone := (S.permanentSite_other n p hfresh h hp).1
      simp [Site.paired, hnone] at hpair
  · rintro ⟨n, h, hpair⟩
    rwa [S.permanentSite_requested n p h]

end Schedule

end UnconditionalCounterexample.Variations.Univariate
