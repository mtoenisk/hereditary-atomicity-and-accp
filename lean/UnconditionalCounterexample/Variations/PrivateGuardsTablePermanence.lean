import UnconditionalCounterexample.Variations.PrivateGuardsTableFamily
import UnconditionalCounterexample.Variations.MultivariateSelectionTablePath
import UnconditionalCounterexample.Variations.MultivariateSelectionEntryModels
import UnconditionalCounterexample.Variations.MultivariateSelectionGuards

/-! # Public places and prior factors on the actual punctured history -/

noncomputable section
namespace UnconditionalCounterexample.Variations.PrivateGuards.Live

open GuardSupport MvPolynomial MultivariateSelection MultiDomain

variable {r d : ℕ} {K : Type*} [Field K] [CharZero K]
  (P : TablePolicy r K) (q : PrimeIndex) (c : Fin (r+1) → ℚ) (C : Config r d)

local notation "liveRule" => tableRule P q c

def publicPath : TablePath r q where
  batch n := (event C liveRule n).entry.memory
  old n := oldPolys (before C liveRule n)
  valid n := by
    have H := liveBatch_valid q n (before C liveRule n)
    rw [← memory_eq P q c C n] at H
    cases n <;> exact H

local notation "T" => publicPath P q c C

theorem path_extra (n : ℕ) : extraPrimes (before C liveRule n) ⊆ ((T).batch n).processed ∧
    ((T).batch n).first.prime ∉ extraPrimes (before C liveRule n) ∧
    ((T).batch n).second.prime ∉ extraPrimes (before C liveRule n) := by
  change extraPrimes _ ⊆ (event C liveRule n).entry.memory.processed ∧
    (event C liveRule n).entry.memory.first.prime ∉ _ ∧ (event C liveRule n).entry.memory.second.prime ∉ _
  rw [memory_eq P q c C n]
  exact liveBatch_extra q n _

theorem private_gt_covered (n : ℕ) (p : PrimeIndex) (hp : p ∈ ((T).table n).covered) :
    p.val < (prime C liveRule n).val := by
  have A := accepted C liveRule n
  apply A.prime_gt
  apply Finset.mem_union_left
  obtain ⟨hi,h⟩ := A.main_ok
  have hr := h.2.2.2.1
  have hm := h.2.1
  change (event C liveRule n).reserved = _ at hr
  rw [hr]
  rw [((T).batch n).covered_eq] at hp
  change p ∈ insert (event C liveRule n).entry.memory.aux (event C liveRule n).entry.memory.processed at hp
  rw [hm] at hp
  simpa only [tablePrescription,Finset.empty_union] using hp

/-- Every private prime is distinct from every public primary prime, including
at its own stage. Hence there are no two indices for a primary on a private fibre. -/
theorem primary_ne_private (j n : ℕ) : ((T).places.primes j) ≠ prime C liveRule n := by
  change ((T).primaryBirth j).prime ≠ _
  by_cases h : n < j/2
  · have he := extra_private (before C liveRule (j/2)) (⟨n,h⟩ : Fin (j/2))
    change prime C liveRule n ∈ extraPrimes (before C liveRule (j/2)) at he
    rcases (T).primary_is_birth j with hb | hb <;> rw [hb]
    · exact fun h' => (path_extra P q c C _).2.1 (h'.symm ▸ he)
    · exact fun h' => (path_extra P q c C _).2.2 (h'.symm ▸ he)
  · exact fun he => (private_gt_covered P q c C n _ ((T).processed_covered n
      ((T).primary_processed j n (Nat.le_of_not_lt h)))).ne (congrArg Subtype.val he)

theorem guarded_tests (n : ℕ) (p : PrimeIndex) (hp : p ∈ ((T).batch n).processed) :
    ∃ N, LocalTests (before C liveRule n) ((T).permanentFibre p) c N
      (MvPolynomial.map (algebraMap ℚ ℚ_[p.val]) (main C liveRule n)) := by
  have hb : (T).batch n = liveBatch q n (before C liveRule n) := memory_eq P q c C n
  let v : (liveBatch q n (before C liveRule n)).processed := ⟨p,(congrArg Batch.processed hb) ▸ hp⟩
  obtain ⟨N,hN⟩ := processed_tests P q c C n v
  have ht (B : Batch r n) (he : B = (T).batch n) (h : p ∈ B.table.covered) :
      B.table.fibre p h = (T).permanentFibre p := by subst B; exact (T).frozen _
  exact ⟨N,(congrArg (fun F : Fibre r p => LocalTests (before C liveRule n) F c N
    (MvPolynomial.map (algebraMap ℚ ℚ_[p.val]) (main C liveRule n))) (ht _ hb.symm _)).mp hN⟩

private theorem mem_old {n : ℕ} (h : History r (Batch r) n) (i : Fin n) :
    (h i).entry.raw i.val ∈ oldPolys h ∧ (h i).puncture ∈ oldPolys h := by
  classical
  exact ⟨Finset.mem_union_left _ (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩),
    Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩)⟩

theorem main_mem_old {j n : ℕ} (hj : j < n) : main C liveRule j ∈ (T).old n :=
  (mem_old (before C liveRule n) ⟨j,hj⟩).1

theorem puncture_mem_old {j n : ℕ} (hj : j < n) : puncture C liveRule j ∈ (T).old n :=
  (mem_old (before C liveRule n) ⟨j,hj⟩).2

theorem first_not_dvd_main (n : ℕ) : ¬ X 0 ∣ main C liveRule n := by
  intro h
  obtain ⟨hi,H⟩ := (accepted C liveRule n).main_ok
  have hrev := (X_prime.irreducible.associated_of_dvd (event C liveRule n).irreducible h).symm.dvd
  have hdeg := totalDegree_le_of_dvd_of_isDomain hrev (X_ne_zero (R := ℚ) (0 : Fin (r+1)))
  have hh := H.2.2.1
  change (main C liveRule n).totalDegree = _ at hh
  rw [hh,totalDegree_X] at hdeg
  exact (Nat.not_succ_le_self 1) ((tablePrescription P q c (before C liveRule n) hi).degree_two.trans hdeg)

theorem first_not_dvd_puncture (n : ℕ) : ¬ X 0 ∣ puncture C liveRule n := fun h =>
  puncture_not_dvd_seed C liveRule n (X_prime.irreducible.associated_of_dvd (event C liveRule n).irreducible_puncture h).symm.dvd

theorem primary_old_main (j n : ℕ) (hn : n < j/2) :
    ((T).places.primary j).valuation (algebraMap _ (FunctionField (r+1)) (main C liveRule n)) = 1 := by
  classical
  apply ((T).primaryBirth j).old_units
  rw [((T).valid _).previous_eq]
  exact Finset.mem_filter.mpr ⟨main_mem_old P q c C hn,first_not_dvd_main P q c C n⟩

theorem primary_old_puncture (j n : ℕ) (hn : n < j/2) :
    ((T).places.primary j).valuation (algebraMap _ (FunctionField (r+1)) (puncture C liveRule n)) = 1 := by
  classical
  apply ((T).primaryBirth j).old_units
  rw [((T).valid _).previous_eq]
  exact Finset.mem_filter.mpr ⟨puncture_mem_old P q c C hn,first_not_dvd_puncture P q c C n⟩

end UnconditionalCounterexample.Variations.PrivateGuards.Live
