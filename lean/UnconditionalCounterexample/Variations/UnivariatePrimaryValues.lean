import UnconditionalCounterexample.Variations.UnivariateClient
import UnconditionalCounterexample.Variations.UnivariateValues

/-!
# Actual primary birth numbers and values

The birth clock of a processed guard identifies the primary coordinate at its
prime. A normalized-value prescription indexed by this clock gives the global
profile of every selected generator, including at primaries born after it.
-/

noncomputable section

namespace UnconditionalCounterexample.Variations.UnivariateClient.Family

open Polynomial GuardSupport PrimaryChoices CombinedGuardStep RecursivePrefix Univariate MixedStageSelection

variable (F : Family)

theorem prime_processed {birth raw : ℕ} (h : birth ≤ raw) :
    F.prime birth ∈ (selection F.requirements raw).batch.processed.primes := by
  have hmem := F.schedule.requested_processed birth (F.mem_chosen birth)
  rcases eq_or_lt_of_le h with rfl | hlt
  · exact hmem
  · rw [(selection F.requirements raw).progress.processed]
    exact Finset.mem_union_left _ (Finset.mem_union_left _ (assigned_mono F.requirements hlt
      ((selection F.requirements birth).batch.processed_subset_assigned hmem)))

theorem prime_birth (n : ℕ) : (chain F.requirements).guardChain.birth (F.prime n) = n := by
  let C := (chain F.requirements).guardChain
  have hp : F.prime n ∈ (C.assignments n).primes :=
    (selection F.requirements n).batch.processed_subset_assigned (F.prime_processed le_rfl)
  have hn := (C.birth_le_iff_mem _ _).mpr hp
  apply le_antisymm hn
  by_contra! hlt
  have : F.prime n ∈ ((chain F.requirements).approx n).state.assignment.primes :=
    assigned_mono F.requirements hlt (C.birth_mem (F.prime n))
  exact (F.atStage n).fresh this

/-- At every later stage that uses a primary, its stored birth field is the
index in the global series of chosen primary primes. -/
theorem guardAt_birth {raw birth : ℕ} (i : (selection F.requirements raw).batch.indices)
    (hp : primes i.val = F.prime birth) : ((selection F.requirements raw).batch.guardAt i).birth = birth := by
  let C := (chain F.requirements).guardChain
  let B := (selection F.requirements raw).batch
  let p := primes i.val
  have hm : p ∈ B.processed.primes := (B.mem_indices _).mp i.property
  have ha : p ∈ (C.assignments raw).primes := B.processed_subset_assigned hm
  have he := C.guard_agrees raw p ha
  change B.assigned.guard p _ = C.guard p at he
  rw [B.assigned_old p hm] at he
  change (B.processed.guard p hm).birth = _
  rw [he, C.guard_birth]
  exact (congrArg C.birth hp).trans (F.prime_birth birth)

theorem prime_active (n : ℕ) :
    Active (permanentSite F.requirements (F.prime n)).paired false :=
  Or.inr ((F.paired_iff _).mpr ⟨n, rfl⟩)

/-- Later primary choices were explicitly screened against every old raw
polynomial. Hence earlier normalized generators evaluate to units there. -/
theorem before_birth_norm {raw birth : ℕ} (h : raw < birth) :
    ‖(permanentSite F.requirements (F.prime birth)).evaluate false (F.prime_active birth)
      ((chain F.requirements).generators raw)‖ = 1 :=
  generator_norm_before_birth F.schedule _ (F.mem_chosen birth) rfl
    (F.atStage birth).old_primary_units raw h

/-- Turn the finite target-norm calculation into the global primary
norm formula for every generator and every birth index. -/
theorem generator_primary_norm (order : ℕ → ℕ → ℕ)
    (hpre : ∀ raw birth, raw < birth → order raw birth = 0)
    (hnorm : ∀ raw (i : (selection F.requirements raw).batch.indices),
      Active (selectionSite F.requirements raw i).paired false →
      ‖(actualTargets F.requirements raw).value i false‖ =
        ((primes i.val).val : ℝ) ^ (-(order raw ((selection F.requirements raw).batch.guardAt i).birth : ℤ)))
    (raw birth : ℕ) :
    ‖(permanentSite F.requirements (F.prime birth)).evaluate false (F.prime_active birth)
      ((chain F.requirements).generators raw)‖ = ((F.prime birth).val : ℝ) ^ (-(order raw birth : ℤ)) := by
  by_cases h : raw < birth
  · rw [F.before_birth_norm h, hpre raw birth h]
    simp
  · have hmem := F.prime_processed (Nat.le_of_not_gt h)
    have aux (p : PrimeIndex) (he : p = F.prime birth)
        (hm : p ∈ (selection F.requirements raw).batch.processed.primes)
        (ha : Active (permanentSite F.requirements p).paired false) :
        ‖(permanentSite F.requirements p).evaluate false ha ((chain F.requirements).generators raw)‖ =
          (p.val : ℝ) ^ (-(order raw birth : ℤ)) := by
      obtain ⟨j, rfl⟩ := primes.surjective p
      let B := (selection F.requirements raw).batch
      let i : B.indices := ⟨j, (B.mem_indices j).mpr hm⟩
      have ha' : Active (selectionSite F.requirements raw i).paired false := by
        rw [selectionSite_eq]
        exact ha
      have val := (processed_value F.requirements raw i false ha).1.trans (hnorm raw i ha')
      rw [F.guardAt_birth i he] at val
      exact val
    exact aux _ rfl hmem (F.prime_active birth)

end UnconditionalCounterexample.Variations.UnivariateClient.Family
