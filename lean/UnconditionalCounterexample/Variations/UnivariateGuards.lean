import UnconditionalCounterexample.Variations.UnivariateCentres

/-!
# Permanent guard choices for the two-centre recursion

At birth choose a guard over 2 congruent to 3 modulo 4 and an odd guard
avoiding both centres. The old guards are copied at every successor. The
ordinary batch may include any finite primary request beyond its cutoff.
-/

noncomputable section

namespace UnconditionalCounterexample.Variations.UnivariateGuards

open Polynomial GuardSupport PaperGuardStages CombinedGuardStep RecursivePrefix

/-- The conditions for the seed functions at a guard of the two-centre construction. Every
`Guard` already has nonzero residue. -/
structure Good {p : PrimeIndex} (g : Guard p) : Prop where
  dyadic : p.val = 2 → PadicInt.toZModPow 2 g.value = 3
  odd : p.val ≠ 2 → PadicInt.toZMod g.value ≠ 1

/-- The dyadic choice is independent of the finite cutoff; a first-batch odd
guard may use the residue 2, even at the prime 3. -/
theorem exists_initial_guard (p : PrimeIndex) : ∃ g : Guard p, g.birth = 0 ∧ Good g := by
  rcases p with ⟨p, hp⟩
  by_cases h2 : p = 2
  · subst p
    obtain ⟨β, ht, hu, hmod⟩ := UnivariateCentres.exists_dyadic_guard
    exact ⟨⟨β, ht, hu, (PadicInt.toZMod β).val, (ZMod.natCast_zmod_val _).symm, 0, by omega⟩, rfl,
      fun _ => hmod, fun hn => (hn rfl).elim⟩
  · let _ : Fact p.Prime := ⟨hp⟩
    have hgt : 2 < p := lt_of_le_of_ne hp.two_le (Ne.symm h2)
    obtain ⟨β, ht, hu, hr, _⟩ := EvaluationChoices.exists_transcendental_unit_residue p 2
      (by intro hd; exact (not_le_of_gt hgt) (Nat.le_of_dvd (by decide) hd))
    refine ⟨⟨β, ht, hu, 2, hr, 0, by omega⟩, rfl, fun h => (h2 h).elim, fun _ => ?_⟩
    change PadicInt.toZMod β ≠ 1
    rw [hr]
    intro h
    have hm := (ZMod.natCast_eq_natCast_iff' 2 1 p).mp (by simpa using h)
    rw [Nat.mod_eq_of_lt hgt, Nat.mod_eq_of_lt hp.one_lt] at hm
    contradiction

private theorem exists_processed {n : ℕ} (P : Prefix n) (start : n = 0 → P.state = zeroState)
    (M : ℕ) (needed : Finset PrimeIndex) :
    ∃ A : Assignment, A.primes = nextPrimes P.state.assignment M needed ∧
      P.state.assignment.primes ⊆ A.primes ∧
      (∀ p (hp : p ∈ P.state.assignment.primes) (hpA : p ∈ A.primes),
        A.guard p hpA = P.state.assignment.guard p hp) ∧
      ∀ p (hp : p ∈ A.primes), p ∉ P.state.assignment.primes →
        (A.guard p hp).birth = n ∧ Good (A.guard p hp) ∧
          ∀ j : Fin n, ‖(P.raw j).eval₂ (algebraMap ℚ ℚ_[p.val]) (A.guard p hp).value.val‖ = 1 := by
  classical
  by_cases hn : n = 0
  · subst n
    let A : Assignment := ⟨nextPrimes P.state.assignment M needed,
      fun p _ => (exists_initial_guard p).choose⟩
    refine ⟨A, rfl, subset_nextPrimes _ _ _, ?_, ?_⟩
    · intro p hp
      simp [start rfl, zeroState] at hp
    · intro p _ _
      exact ⟨(exists_initial_guard p).choose_spec.1,
        (exists_initial_guard p).choose_spec.2, fun j => Fin.elim0 j⟩
  · have hcover := old_degree_cutoff_covered P.state P.raw (P.current_degree_budget hn)
    obtain ⟨A, hA, hsub, hold, hnew⟩ := RationalGuardStage.exists_rational_stage_transition
      P.state.assignment P.raw P.monic P.current_support n M needed hcover
    refine ⟨A, hA, hsub, hold, ?_⟩
    intro p hp hprev
    obtain ⟨hb, hr, hraw⟩ := hnew p hp hprev
    have hlt := large_of_unassigned _ _ hcover p hprev
    have h₁ : 2 ^ 4 ≤ 2 ^ (4 + ∑ j, (P.raw j).natDegree) :=
      Nat.pow_le_pow_right (by decide) (Nat.le_add_right _ _)
    have h₂ : p.val ≠ 2 := by omega
    exact ⟨hb, ⟨fun h => (h₂ h).elim, fun _ => hr⟩, hraw⟩

/-- Every finite batch has the cutoff, requested primes, old guard
persistence and old-raw unit evaluations of the common recursion. Each new
guard is suitable for the literal two seed functions. -/
theorem exists_processing_batch {n : ℕ} (P : Prefix n) (start : n = 0 → P.state = zeroState)
    (degree : ℕ) (needed : Finset PrimeIndex) :
    ∃ B : Batch, StageRecursion.BatchProgress P degree needed B ∧
      ∀ p (hp : p ∈ B.assigned.primes), p ∉ P.state.assignment.primes →
        Good (B.assigned.guard p hp) := by
  classical
  let M := RationalGuardStage.nextCutoff P.raw P.state.cutoff n degree
  obtain ⟨hM, _, hdeg⟩ := RationalGuardStage.nextCutoff_bounds P.raw P.state.cutoff n degree
  obtain ⟨A, hA, hsub, hold, hnew⟩ := exists_processed P start M needed
  have hcover : GuardStages.primesThrough M ⊆ A.primes := hA ▸ cutoff_subset_nextPrimes _ _ _
  obtain ⟨ell, g, hell, hfresh, hbirth, hres, hraw⟩ :=
    RationalGuardStage.exists_rational_auxiliary_guard A P.raw P.monic
      (fun j i p hd => hsub (P.current_support j i p hd)) n M
  let B : Batch := ⟨n, M, A, hcover, ell, hell, hfresh, g, hbirth, hres⟩
  have h₂ : ell.val ≠ 2 := by
    have hmin : 2 ^ 4 ≤ 2 ^ (4 + (∑ j, (P.raw j).natDegree) + degree) :=
      Nat.pow_le_pow_right (by decide) (by omega)
    change 2 ^ (4 + (∑ j, (P.raw j).natDegree) + degree) < M at hdeg
    omega
  refine ⟨B, ⟨rfl, hA, ?_, ?_, hM, hdeg.le⟩, ?_⟩
  · intro p hp hpB
    rw [B.assigned_old p (hsub hp)]
    exact hold p hp (hsub hp)
  · intro p hpB hp
    rcases Finset.mem_insert.mp hpB with he | hpA
    · subst p
      rw [B.assigned_auxiliary]
      exact ⟨hbirth, hraw⟩
    · rw [B.assigned_old p hpA]
      exact ⟨(hnew p hpA hp).1, (hnew p hpA hp).2.2⟩
  · intro p hpB hp
    rcases Finset.mem_insert.mp hpB with he | hpA
    · subst p
      rw [B.assigned_auxiliary]
      exact ⟨fun h => (h₂ h).elim, fun _ => hres⟩
    · rw [B.assigned_old p hpA]
      exact (hnew p hpA hp).2.1

/-- The base processing callback for a schedule with two-centre guards. -/
def base {n : ℕ} (P : Prefix n) (start : n = 0 → P.state = zeroState)
    (degree : ℕ) (needed : Finset PrimeIndex) :
    {B : Batch // StageRecursion.BatchProgress P degree needed B} :=
  ⟨(exists_processing_batch P start degree needed).choose,
    (exists_processing_batch P start degree needed).choose_spec.1⟩

theorem base_good {n : ℕ} (P : Prefix n) (start : n = 0 → P.state = zeroState)
    (degree : ℕ) (needed : Finset PrimeIndex) (p : PrimeIndex)
    (hp : p ∈ (base P start degree needed).val.assigned.primes)
    (hf : p ∉ P.state.assignment.primes) :
    Good ((base P start degree needed).val.assigned.guard p hp) :=
  (exists_processing_batch P start degree needed).choose_spec.2 p hp hf

end UnconditionalCounterexample.Variations.UnivariateGuards
