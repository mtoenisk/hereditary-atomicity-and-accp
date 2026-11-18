import UnconditionalCounterexample.RationalGuardStage

/-!
The batch stage is the zero-based raw-prefix/birth clock. In particular the
first guard batch has stage zero. The positive arithmetic stage passed to
SignedConstant and FiniteStageSelection is this clock plus one, matching the
manuscript's stages i = 1, 2, ... . A common recursive consumer must increment
the birth clock along with its actual raw prefix; the generic successor theorem
accepts that clock as an explicit argument and does not itself run a recursion.
-/

namespace UnconditionalCounterexample.CombinedGuardStep

open Polynomial GuardSupport PaperGuardStages RationalGuardStage

/-- The finite guard projection retained between common raw-polynomial stages. -/
structure State where
  cutoff : ℕ
  assignment : Assignment
  covered : GuardStages.primesThrough cutoff ⊆ assignment.primes

/-- The ordinary processing set determines coefficient denominator support;
the auxiliary prime is separately fresh and is then retained in the next state. -/
structure Batch where
  stage : ℕ
  cutoff : ℕ
  processed : Assignment
  covered : GuardStages.primesThrough cutoff ⊆ processed.primes
  auxiliary : PrimeIndex
  auxiliary_large : cutoff < auxiliary.val
  auxiliary_fresh : auxiliary ∉ processed.primes
  auxiliary_guard : Guard auxiliary
  auxiliary_birth : auxiliary_guard.birth = stage
  auxiliary_away_one : PadicInt.toZMod auxiliary_guard.value ≠ 1

noncomputable def Batch.assigned (B : Batch) : Assignment :=
  B.processed.insert B.auxiliary B.auxiliary_guard

@[simp] theorem Batch.assigned_primes (B : Batch) :
    B.assigned.primes = Insert.insert B.auxiliary B.processed.primes := rfl

theorem Batch.processed_subset_assigned (B : Batch) : B.processed.primes ⊆ B.assigned.primes := by
  intro p hp
  exact Finset.mem_insert_of_mem hp

theorem Batch.assigned_old (B : Batch) (p : PrimeIndex) (hp : p ∈ B.processed.primes) :
    B.assigned.guard p (B.processed_subset_assigned hp) = B.processed.guard p hp :=
  B.processed.insert_old B.auxiliary B.auxiliary_guard p hp

theorem Batch.assigned_auxiliary (B : Batch) :
    B.assigned.guard B.auxiliary (Finset.mem_insert_self _ _) = B.auxiliary_guard :=
  B.processed.insert_fresh B.auxiliary B.auxiliary_guard B.auxiliary_fresh

noncomputable def Batch.toState (B : Batch) : State :=
  ⟨B.cutoff, B.assigned, B.covered.trans B.processed_subset_assigned⟩

/-- The literal empty initial guard state has no hidden small-prime obligation. -/
def zeroState : State where
  cutoff := 0
  assignment := ⟨∅, fun p hp => False.elim ((Finset.notMem_empty p) hp)⟩
  covered := by
    intro p hp
    have hval := (GuardStages.mem_primesThrough p 0).mp hp
    exact False.elim ((Nat.not_le_of_gt p.property.pos) hval)

/-- The first ordinary batch uses the paper's arbitrary nonzero residues;
its auxiliary guard still uses the logarithmic rule and avoids residue one. -/
theorem exists_initial_batch (newDegree : ℕ) (required : Finset PrimeIndex) :
    ∃ B : Batch, B.stage = 0 ∧ B.cutoff = 2 ^ (4 + newDegree) + 1 ∧
      B.processed.primes = GuardStages.primesThrough B.cutoff ∪ required ∧
      zeroState.assignment.primes ⊆ B.assigned.primes ∧
      ∀ p (hp : p ∈ B.assigned.primes), (B.assigned.guard p hp).birth = 0 := by
  classical
  let M := 2 ^ (4 + newDegree) + 1
  obtain ⟨A, hA, hbirth⟩ := exists_initial_assignment (GuardStages.primesThrough M ∪ required)
  have hcover : GuardStages.primesThrough M ⊆ A.primes := by
    rw [hA]
    exact Finset.subset_union_left
  let F (p : PrimeIndex) (j : Fin 0) : ℤ_[p.val][X] := Fin.elim0 j
  obtain ⟨ell, g, hell, hfresh, hg, hres, _⟩ := PaperGuardStages.exists_fresh_auxiliary_guard
    A 0 0 M (Finset.univ : Finset (Fin 0)) F
    (fun _ _ j _ => Fin.elim0 j) (by intro p _; simp)
  let B : Batch := ⟨0, M, A, hcover, ell, hell, hfresh, g, hg, hres⟩
  refine ⟨B, rfl, rfl, hA, Finset.empty_subset _, ?_⟩
  intro p hp
  rcases Finset.mem_insert.mp hp with heq | hpA
  · subst p
    rw [B.assigned_auxiliary]
    exact hg
  · rw [B.assigned_old p hpA]
    exact hbirth p hpA

/-- The previous cutoff and its coverage give the required old-degree bound
at every currently unassigned prime. -/
theorem old_degree_cutoff_covered {J : Type*} [Fintype J] (A : State) (Q : J → ℚ[X])
    (hbudget : 2 ^ (4 + ∑ j, (Q j).natDegree) ≤ A.cutoff) :
    GuardStages.primesThrough (2 ^ (4 + ∑ j, (Q j).natDegree)) ⊆ A.assignment.primes := by
  intro p hp
  apply A.covered
  apply (GuardStages.mem_primesThrough p A.cutoff).mpr
  exact ((GuardStages.mem_primesThrough p _).mp hp).trans hbudget

/-- One combined guard assignment step. Ordinary primes, coefficient support,
and the fresh auxiliary prime remain distinguished. The final finite assignment
contains and literally preserves every previously assigned guard. -/
theorem exists_successor_batch {J : Type*} [Fintype J]
    (A : State) (Q : J → ℚ[X]) (hQ : ∀ j, (Q j).Monic)
    (hsupp : ∀ j n (p : PrimeIndex), p.val ∣ ((Q j).coeff n).den → p ∈ A.assignment.primes)
    (hbudget : 2 ^ (4 + ∑ j, (Q j).natDegree) ≤ A.cutoff)
    (i newDegree : ℕ) (required : Finset PrimeIndex) :
    ∃ B : Batch, B.stage = i ∧ B.cutoff = nextCutoff Q A.cutoff i newDegree ∧
      B.processed.primes = nextPrimes A.assignment B.cutoff required ∧
      A.cutoff < B.cutoff ∧
      2 ^ (4 + (∑ j, (Q j).natDegree) + newDegree) < B.cutoff ∧
      A.assignment.primes ⊆ B.assigned.primes ∧
      (∀ p (hp : p ∈ A.assignment.primes) (hpB : p ∈ B.assigned.primes),
        B.assigned.guard p hpB = A.assignment.guard p hp) ∧
      ∀ p (hp : p ∈ B.assigned.primes), p ∉ A.assignment.primes →
        (B.assigned.guard p hp).birth = i ∧
        ∀ j, ‖(Q j).eval₂ (algebraMap ℚ ℚ_[p.val]) (B.assigned.guard p hp).value.val‖ = 1 := by
  classical
  let M := nextCutoff Q A.cutoff i newDegree
  obtain ⟨P, hP, hAP, hold, hnew⟩ := exists_rational_stage_transition A.assignment Q hQ hsupp
    i M required (old_degree_cutoff_covered A Q hbudget)
  have hcover : GuardStages.primesThrough M ⊆ P.primes := by
    rw [hP]
    exact cutoff_subset_nextPrimes A.assignment M required
  have hsuppP : ∀ j n (p : PrimeIndex), p.val ∣ ((Q j).coeff n).den → p ∈ P.primes :=
    fun j n p hp => hAP (hsupp j n p hp)
  obtain ⟨ell, g, hell, hfresh, hg, hres, hraw⟩ :=
    exists_rational_auxiliary_guard P Q hQ hsuppP i M
  let B : Batch := ⟨i, M, P, hcover, ell, hell, hfresh, g, hg, hres⟩
  have hAB : A.assignment.primes ⊆ B.assigned.primes := hAP.trans B.processed_subset_assigned
  refine ⟨B, rfl, rfl, hP, (nextCutoff_bounds Q A.cutoff i newDegree).1,
    (nextCutoff_bounds Q A.cutoff i newDegree).2.2, hAB, ?_, ?_⟩
  · intro p hp hpB
    have hpP := hAP hp
    rw [B.assigned_old p hpP]
    exact hold p hp hpP
  · intro p hp hn
    rcases Finset.mem_insert.mp hp with heq | hpP
    · subst p
      rw [B.assigned_auxiliary]
      exact ⟨hg, hraw⟩
    · rw [B.assigned_old p hpP]
      exact ⟨(hnew p hpP hn).1, (hnew p hpP hn).2.2⟩

end UnconditionalCounterexample.CombinedGuardStep
