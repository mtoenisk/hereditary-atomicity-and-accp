import UnconditionalCounterexample.Variations.MultivariateSelectionFrozen
import UnconditionalCounterexample.Variations.GuardFiniteSupport

/-! # Permanent places extracted from a chronological table of batches -/

noncomputable section
namespace UnconditionalCounterexample.MultivariateSelection

open MvPolynomial GuardSupport Variations MultiDomain

variable {r : ℕ} {q : PrimeIndex}

def previousTable (B : (n : ℕ) → Batch r n) : ℕ → SiteTable r
  | 0 => SiteTable.empty r
  | n+1 => (B n).table

/-- The screened list may contain both the main and puncture polynomials. -/
structure TablePath (r : ℕ) (q : PrimeIndex) where
  batch : (n : ℕ) → Batch r n
  old : ℕ → Finset (Poly r)
  valid : ∀ n, (batch n).Valid q (previousTable batch n) (old n)

namespace TablePath
variable (T : TablePath r q)

abbrev table (n : ℕ) := (T.batch n).table

theorem table_grows (n : ℕ) : (table T n).Extends (table T (n+1)) :=
  (T.valid (n+1)).extends_old

theorem table_grows_of_le {i j : ℕ} (hij : i ≤ j) : (table T i).Extends (table T j) := by
  induction hij with
  | refl => exact ⟨fun _ h => h,fun _ _ => rfl⟩
  | step h ih => exact ih.trans (table_grows T _)

theorem processed_covered (n : ℕ) : (T.batch n).processed ⊆ (table T n).covered := by
  rw [(T.batch n).covered_eq]
  exact Finset.subset_insert _ _

theorem guard_covered (p : PrimeIndex) : p ∈ (table T (PrimaryChoices.primes.symm p)).covered := by
  apply processed_covered
  simpa using (T.valid (PrimaryChoices.primes.symm p)).enumerated

def permanentFibre (p : PrimeIndex) : Fibre r p :=
  (table T (PrimaryChoices.primes.symm p)).fibre p (guard_covered T p)

theorem frozen {n : ℕ} {p : PrimeIndex} (hp : p ∈ (table T n).covered) :
    (table T n).fibre p hp = permanentFibre T p := by
  obtain h | h := le_total n (PrimaryChoices.primes.symm p)
  · exact ((table_grows_of_le T h).choose_spec p hp).symm
  · exact (table_grows_of_le T h).choose_spec p (guard_covered T p)

/-- First chronological assignment. The prime may appear as a primary, an
enumerated guard, the reserved prime, or the fresh auxiliary guard. -/
def firstAppearance (p : PrimeIndex) : ℕ :=
  Nat.find (show ∃ n, p ∈ (table T n).covered from ⟨_,guard_covered T p⟩)

theorem first_mem (p : PrimeIndex) : p ∈ (table T (firstAppearance T p)).covered :=
  Nat.find_spec (show ∃ n, p ∈ (table T n).covered from ⟨_,guard_covered T p⟩)

theorem first_le {p : PrimeIndex} {n : ℕ} (hp : p ∈ (table T n).covered) : firstAppearance T p ≤ n :=
  Nat.find_min' (show ∃ n, p ∈ (table T n).covered from ⟨_,guard_covered T p⟩) hp

theorem new_at_first (p : PrimeIndex) :
    p ∉ (previousTable T.batch (firstAppearance T p)).covered := by
  generalize hN : firstAppearance T p = n
  cases n with
  | zero => exact Finset.notMem_empty _
  | succ n =>
    intro h
    exact (by have := first_le T (show p ∈ (table T n).covered from h); omega)

theorem eventual_processed (p : PrimeIndex)
    {n : ℕ} (hn : firstAppearance T p < n) : p ∈ (T.batch n).processed := by
  cases n with
  | zero => omega
  | succ n =>
    exact (T.valid (n+1)).copied ((table_grows_of_le T (Nat.le_of_lt_succ hn)).choose (first_mem T p))

theorem not_processed_cases {p : PrimeIndex} {n : ℕ} (hp : p ∉ (T.batch n).processed) :
    n < firstAppearance T p ∨ (n = firstAppearance T p ∧ p = (T.batch n).aux) := by
  have hn : n ≤ firstAppearance T p := le_of_not_gt (fun h => hp (eventual_processed T p h))
  rcases hn.lt_or_eq with h | h
  · exact Or.inl h
  · refine Or.inr ⟨h,?_⟩
    have hm : p ∈ (table T n).covered := h ▸ first_mem T p
    rw [(T.batch n).covered_eq] at hm
    exact (Finset.mem_insert.mp hm).resolve_right hp

theorem frozen_guard_avoids (p : PrimeIndex) :
    let n := firstAppearance T p
    ∀ f ∈ screen n p (T.old n) (decide (p = (T.batch n).aux)),
      f ≠ 0 → (permanentFibre T p).guard.avoids f := by
  intro n f hf hne
  rw [← frozen T (first_mem T p)]
  exact (T.valid n).guards p _ (new_at_first T p) f hf hne

theorem permanent_guard_test {p : PrimeIndex} (f : ResiduePolys r p)
    (hf : f ∈ guardTests r (firstAppearance T p) p) (hne : f ≠ 0) : (permanentFibre T p).guard.avoids f :=
  frozen_guard_avoids T p f (Finset.mem_union_left _ (Finset.mem_union_left _ hf)) hne

theorem earlier_guard_avoids {p : PrimeIndex} {f : Poly r}
    (hf : f ∈ T.old (firstAppearance T p)) (hne : reduction p f ≠ 0) :
    (permanentFibre T p).guard.avoids (reduction p f) := by
  apply frozen_guard_avoids T p _ (Finset.mem_union_left _ (Finset.mem_union_right _ ?_)) hne
  exact Finset.mem_image_of_mem _ hf

private theorem exists_primaryBirth (j : ℕ) :
    ∃ B : PrimaryBirth r j (firstOrder j) (T.batch (j/2)).previous,
      (permanentFibre T B.prime).primary = some (j,B.tuple) ∧ B.prime ∈ (T.batch (j/2)).processed ∧
        (B.prime = (T.batch (j/2)).first.prime ∨ B.prime = (T.batch (j/2)).second.prime) := by
  obtain ⟨n,rfl | rfl⟩ : ∃ n, j = 2*n ∨ j = 2*n+1 := ⟨j/2,by omega⟩
  · rw [show 2*n/2 = n by omega]
    let v := T.valid n
    exact ⟨(T.batch n).first,(congrArg Fibre.primary (frozen T (processed_covered T n v.first_mem))).symm.trans (v.first_at _), v.first_mem,Or.inl rfl⟩
  · rw [show (2*n+1)/2 = n by omega]
    let v := T.valid n
    exact ⟨(T.batch n).second,(congrArg Fibre.primary (frozen T (processed_covered T n v.second_mem))).symm.trans (v.second_at _), v.second_mem,Or.inr rfl⟩

def primaryBirth (j : ℕ) : PrimaryBirth r j (firstOrder j) (T.batch (j/2)).previous :=
  (exists_primaryBirth T j).choose

theorem primary_fibre (j : ℕ) :
    (permanentFibre T (primaryBirth T j).prime).primary = some (j,(primaryBirth T j).tuple) :=
  (exists_primaryBirth T j).choose_spec.1

theorem primary_at_birth (j : ℕ) : (primaryBirth T j).prime ∈ (T.batch (j/2)).processed :=
  (exists_primaryBirth T j).choose_spec.2.1

theorem primary_is_birth (j : ℕ) :
    (T.primaryBirth j).prime = (T.batch (j/2)).first.prime ∨
    (T.primaryBirth j).prime = (T.batch (j/2)).second.prime :=
  (exists_primaryBirth T j).choose_spec.2.2

theorem processed_mono {i j : ℕ} (h : i ≤ j) :
    (T.batch i).processed ⊆ (T.batch j).processed := by
  induction h with
  | refl => exact fun _ hp => hp
  | step h ih => exact fun _ hp => (T.valid _).copied (processed_covered T _ (ih hp))

theorem primary_processed (j n : ℕ) (h : j/2 ≤ n) : (primaryBirth T j).prime ∈ (T.batch n).processed :=
  processed_mono T h (primary_at_birth T j)

theorem primary_label (j : ℕ) :
    (permanentFibre T (primaryBirth T j).prime).primary.map Prod.fst = some j := by
  rw [primary_fibre]
  rfl

def places : Places (r+1) where
  primes j := (primaryBirth T j).prime
  injective := by
    intro i j h
    change (primaryBirth T i).prime = (primaryBirth T j).prime at h
    apply Option.some.inj
    rw [← primary_label T i, ← primary_label T j,h]
  primary j := (primaryBirth T j).tuple
  guardField p := GuardUnramified.LocalField p.val (GaloisField p.val (permanentFibre T p).guard.degree)
  guardVal p := GuardUnramified.valuation p.val _
  guard_prime p := GuardUnramified.valuation_prime p.val _
  guard p := (permanentFibre T p).guard.tuple

theorem primary_eventually (z : FunctionField (r+1)) :
    ∀ᶠ j in Filter.atTop, ((places T).primary j).valuation z = tVal z :=
  primaryBirths_stabilize (primaryBirth T) z

theorem reserved_guard_only : (permanentFibre T q).primary = none := by
  let v := T.valid 0
  have hq := processed_covered T 0 v.reserved
  rw [← frozen T hq]
  apply v.other_at
  · exact Finset.notMem_empty _
  · exact fun h => v.first_new (h ▸ Finset.mem_insert_self _ _)
  · exact fun h => v.second_new (Finset.mem_insert_of_mem (h ▸ Finset.mem_insert_self _ _))

theorem finite_guard (z : FunctionField (r+1)) (hz : z ≠ 0) :
    {p | ((permanentFibre T p).guard.tuple.valuation z) ≠ 1}.Finite := by
  apply finite_guard_support (firstAppearance T) _ _ (fun _ _ => permanent_guard_test T _) z hz
  apply Filter.tendsto_atTop.mpr
  intro n
  apply Filter.eventually_cofinite.mpr
  apply (table T n).covered.finite_toSet.subset
  intro p hp
  change ¬ n ≤ firstAppearance T p at hp
  exact (table_grows_of_le T (le_of_lt (lt_of_not_ge hp))).choose (first_mem T p)

end TablePath
end UnconditionalCounterexample.MultivariateSelection
