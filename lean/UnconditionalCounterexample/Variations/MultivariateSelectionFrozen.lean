import UnconditionalCounterexample.Variations.MultivariateSelectionSites

/-!
# The permanent places of the same multivariate polynomial recursion

Each polynomial sees a batch computed from precisely its proper prefix.
The next stage inherits all sites including the previous auxiliary guard.
The permanent rational primary and the finite unramified guard at every
prime therefore define valuations on the same selected function field.
-/

noncomputable section
namespace UnconditionalCounterexample.MultivariateSelection

open MvPolynomial GuardSupport Variations MultiDomain MultivariateListedWords
open scoped Topology

variable {r : ℕ}

abbrev SiteHistory (r n : ℕ) := History r (Batch r) n

def earlierPolys {n : ℕ} (h : SiteHistory r n) : Finset (Poly r) := by
  classical exact Finset.univ.image (fun j : Fin n => (h j).raw j.val)

def priorTable : (n : ℕ) → SiteHistory r n → SiteTable r
  | 0, _ => SiteTable.empty r
  | n+1, h => (h ⟨n,Nat.lt_succ_self n⟩).memory.table

def allocate (q : PrimeIndex) (n : ℕ) (h : SiteHistory r n) : Batch r n :=
  batch q n (priorTable n h) (earlierPolys h)

/-- Local analytic neighborhoods at the actual processed sites, with a target
of degree below the chronological choice. -/
structure AnalyticInput {n : ℕ} (B : Batch r n) (d : ℕ) where
  target : ∀ v : B.processed, MvPolynomial (Fin (r+1)) ℚ_[v.val.val]
  target_lt : ∀ v, (target v).totalDegree < d
  neighborhood : ∀ v : B.processed, Set (((Fin (r+1)) →₀ ℕ) → ℚ_[v.val.val])
  mem_nhds : ∀ v, neighborhood v ∈ 𝓝 (fun m => (target v).coeff m)

structure LocalPrescription (r : ℕ) (q : PrimeIndex) where
  floor : ∀ n, SiteHistory r n → ℕ
  input : ∀ n (h : SiteHistory r n) d, floor n h ≤ d → AnalyticInput (allocate q n h) d

variable {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]

structure Geometry (r : ℕ) (K : Type*) [Field K] where
  point : ℕ → Fin (r+1) → K
  primeEnumeration : ℕ → Ideal (MvPolynomial (Fin (r+1)) K)
  fixed : Finset (Fin (r+1) → K)

variable {q : PrimeIndex} (L : LocalPrescription r q) (G : Geometry r K)

def requirements : Requirements r (Batch r) K where
  point := G.point
  primesEnumeration := G.primeEnumeration
  fixed := G.fixed
  words := triangularWords
  word_pos := triangularWords_pos
  threshold := L.floor
  nextMemory n h _ _ := allocate q n h
  sites n h d hd := by
    let B := allocate q n h
    let v := (batch_valid q n (priorTable n h) (earlierPolys h))
    let a := L.input n h d hd
    exact ⟨B.processed,B.aux,v.aux_fresh,a.target,a.target_lt,a.neighborhood,a.mem_nhds⟩

abbrev siteChain (n : ℕ) := chain (requirements L G) n
abbrev siteRaw (n : ℕ) := raw (requirements L G) n
abbrev permanentBatch (n : ℕ) := (siteChain L G n).memory
abbrev table (n : ℕ) := (permanentBatch L G n).table

theorem actual_batch (n : ℕ) : permanentBatch L G n = allocate q n (fun i : Fin n => siteChain L G i.val) :=
  (chain_accepted (requirements L G) n).memory_eq

theorem valid_batch (n : ℕ) :
    (permanentBatch L G n).Valid q (priorTable n (fun i : Fin n => siteChain L G i.val))
      (earlierPolys (fun i : Fin n => siteChain L G i.val)) := by
  rw [actual_batch]
  exact batch_valid _ _ _ _

theorem table_grows (n : ℕ) : (table L G n).Extends (table L G (n+1)) :=
  (valid_batch L G (n+1)).extends_old

theorem table_grows_of_le {i j : ℕ} (hij : i ≤ j) : (table L G i).Extends (table L G j) := by
  induction hij with
  | refl => exact ⟨fun _ h => h,fun _ _ => rfl⟩
  | step h ih => exact ih.trans (table_grows L G _)

theorem processed_covered (n : ℕ) : (permanentBatch L G n).processed ⊆ (table L G n).covered := by
  rw [(permanentBatch L G n).covered_eq]
  exact Finset.subset_insert _ _

theorem guard_covered (p : PrimeIndex) : p ∈ (table L G (PrimaryChoices.primes.symm p)).covered := by
  apply processed_covered
  simpa using (valid_batch L G (PrimaryChoices.primes.symm p)).enumerated

def permanentFibre (p : PrimeIndex) : Fibre r p :=
  (table L G (PrimaryChoices.primes.symm p)).fibre p (guard_covered L G p)

theorem frozen {n : ℕ} {p : PrimeIndex} (hp : p ∈ (table L G n).covered) :
    (table L G n).fibre p hp = permanentFibre L G p := by
  obtain h | h := le_total n (PrimaryChoices.primes.symm p)
  · exact ((table_grows_of_le L G h).choose_spec p hp).symm
  · exact (table_grows_of_le L G h).choose_spec p (guard_covered L G p)

/-- First chronological assignment. The prime may appear as a primary, an
enumerated guard, the reserved prime, or the fresh auxiliary guard. -/
def firstAppearance (p : PrimeIndex) : ℕ :=
  Nat.find (show ∃ n, p ∈ (table L G n).covered from ⟨_,guard_covered L G p⟩)

theorem first_mem (p : PrimeIndex) : p ∈ (table L G (firstAppearance L G p)).covered :=
  Nat.find_spec (show ∃ n, p ∈ (table L G n).covered from ⟨_,guard_covered L G p⟩)

theorem first_le {p : PrimeIndex} {n : ℕ} (hp : p ∈ (table L G n).covered) : firstAppearance L G p ≤ n :=
  Nat.find_min' (show ∃ n, p ∈ (table L G n).covered from ⟨_,guard_covered L G p⟩) hp

theorem new_at_first (p : PrimeIndex) :
    p ∉ (priorTable (firstAppearance L G p) (fun i => siteChain L G i.val)).covered := by
  generalize hN : firstAppearance L G p = n
  cases n with
  | zero => exact Finset.notMem_empty _
  | succ n =>
    intro h
    exact (by have := first_le L G (show p ∈ (table L G n).covered from h); omega)

theorem eventual_processed (p : PrimeIndex)
    {n : ℕ} (hn : firstAppearance L G p < n) : p ∈ (permanentBatch L G n).processed := by
  cases n with
  | zero => omega
  | succ n =>
    exact (valid_batch L G (n+1)).copied ((table_grows_of_le L G (Nat.le_of_lt_succ hn)).choose (first_mem L G p))

theorem not_processed_cases {p : PrimeIndex} {n : ℕ} (hp : p ∉ (permanentBatch L G n).processed) :
    n < firstAppearance L G p ∨ (n = firstAppearance L G p ∧ p = (permanentBatch L G n).aux) := by
  have hn : n ≤ firstAppearance L G p := le_of_not_gt (fun h => hp (eventual_processed L G p h))
  rcases hn.lt_or_eq with h | h
  · exact Or.inl h
  · refine Or.inr ⟨h,?_⟩
    have hm : p ∈ (table L G n).covered := h ▸ first_mem L G p
    rw [(permanentBatch L G n).covered_eq] at hm
    exact (Finset.mem_insert.mp hm).resolve_right hp

theorem frozen_guard_avoids (p : PrimeIndex) :
    let n := firstAppearance L G p
    ∀ f ∈ screen n p (earlierPolys (fun i : Fin n => siteChain L G i.val)) (decide (p = (permanentBatch L G n).aux)),
      f ≠ 0 → (permanentFibre L G p).guard.avoids f := by
  intro n f hf hne
  rw [← frozen L G (first_mem L G p)]
  exact (valid_batch L G n).guards p _ (new_at_first L G p) f hf hne

theorem permanent_guard_test {p : PrimeIndex} (f : ResiduePolys r p)
    (hf : f ∈ guardTests r (firstAppearance L G p) p) (hne : f ≠ 0) : (permanentFibre L G p).guard.avoids f :=
  frozen_guard_avoids L G p f (Finset.mem_union_left _ (Finset.mem_union_left _ hf)) hne

theorem earlier_guard_avoids {p : PrimeIndex} {i : ℕ} (hi : i < firstAppearance L G p)
    (hne : reduction p (siteRaw L G i) ≠ 0) : (permanentFibre L G p).guard.avoids (reduction p (siteRaw L G i)) := by
  classical
  apply frozen_guard_avoids L G p _ (Finset.mem_union_left _ (Finset.mem_union_right _ ?_)) hne
  apply Finset.mem_image.mpr
  exact ⟨_,Finset.mem_image.mpr ⟨(⟨i,hi⟩ : Fin (firstAppearance L G p)),Finset.mem_univ _,rfl⟩,rfl⟩

theorem primary_at_first (n : ℕ) :
    (permanentFibre L G (permanentBatch L G n).first.prime).primary.map Prod.fst = some (2*n) := by
  let v := valid_batch L G n
  have h := v.first_at (processed_covered L G n v.first_mem)
  rw [← frozen L G (processed_covered L G n v.first_mem),h]
  rfl

theorem primary_at_second (n : ℕ) :
    (permanentFibre L G (permanentBatch L G n).second.prime).primary.map Prod.fst = some (2*n+1) := by
  let v := valid_batch L G n
  have h := v.second_at (processed_covered L G n v.second_mem)
  rw [← frozen L G (processed_covered L G n v.second_mem),h]
  rfl

private theorem exists_primaryBirth (j : ℕ) :
    ∃ B : PrimaryBirth r j (firstOrder j) (permanentBatch L G (j/2)).previous,
      (permanentFibre L G B.prime).primary = some (j,B.tuple) ∧ B.prime ∈ (permanentBatch L G (j/2)).processed := by
  obtain ⟨n,rfl | rfl⟩ : ∃ n, j = 2*n ∨ j = 2*n+1 := ⟨j/2,by omega⟩
  · rw [show 2*n/2 = n by omega]
    let v := valid_batch L G n
    exact ⟨(permanentBatch L G n).first,(congrArg Fibre.primary (frozen L G (processed_covered L G n v.first_mem))).symm.trans (v.first_at _), v.first_mem⟩
  · rw [show (2*n+1)/2 = n by omega]
    let v := valid_batch L G n
    exact ⟨(permanentBatch L G n).second,(congrArg Fibre.primary (frozen L G (processed_covered L G n v.second_mem))).symm.trans (v.second_at _), v.second_mem⟩

def primaryBirth (j : ℕ) : PrimaryBirth r j (firstOrder j) (permanentBatch L G (j/2)).previous :=
  (exists_primaryBirth L G j).choose

theorem primary_fibre (j : ℕ) :
    (permanentFibre L G (primaryBirth L G j).prime).primary = some (j,(primaryBirth L G j).tuple) :=
  (exists_primaryBirth L G j).choose_spec.1

theorem primary_at_birth (j : ℕ) : (primaryBirth L G j).prime ∈ (permanentBatch L G (j/2)).processed :=
  (exists_primaryBirth L G j).choose_spec.2

theorem processed_mono {i j : ℕ} (h : i ≤ j) :
    (permanentBatch L G i).processed ⊆ (permanentBatch L G j).processed := by
  induction h with
  | refl => exact fun _ hp => hp
  | step h ih => exact fun _ hp => (valid_batch L G _).copied (processed_covered L G _ (ih hp))

theorem primary_processed (j n : ℕ) (h : j/2 ≤ n) : (primaryBirth L G j).prime ∈ (permanentBatch L G n).processed :=
  processed_mono L G h (primary_at_birth L G j)

theorem primary_label (j : ℕ) :
    (permanentFibre L G (primaryBirth L G j).prime).primary.map Prod.fst = some j := by
  rw [primary_fibre]
  rfl

def places : Places (r+1) where
  primes j := (primaryBirth L G j).prime
  injective := by
    intro i j h
    change (primaryBirth L G i).prime = (primaryBirth L G j).prime at h
    apply Option.some.inj
    rw [← primary_label L G i, ← primary_label L G j,h]
  primary j := (primaryBirth L G j).tuple
  guardField p := GuardUnramified.LocalField p.val (GaloisField p.val (permanentFibre L G p).guard.degree)
  guardVal p := GuardUnramified.valuation p.val _
  guard_prime p := GuardUnramified.valuation_prime p.val _
  guard p := (permanentFibre L G p).guard.tuple

theorem primary_eventually (z : FunctionField (r+1)) :
    ∀ᶠ j in Filter.atTop, ((places L G).primary j).valuation z = tVal z :=
  primaryBirths_stabilize (primaryBirth L G) z

theorem reserved_guard_only : (permanentFibre L G q).primary = none := by
  let v := valid_batch L G 0
  have hq := processed_covered L G 0 v.reserved
  rw [← frozen L G hq]
  apply v.other_at
  · exact Finset.notMem_empty _
  · exact fun h => v.first_new (h ▸ Finset.mem_insert_self _ _)
  · exact fun h => v.second_new (Finset.mem_insert_of_mem (h ▸ Finset.mem_insert_self _ _))

end UnconditionalCounterexample.MultivariateSelection
