import UnconditionalCounterexample.Variations.DyadicRounds
import UnconditionalCounterexample.Variations.FreezingCalendar

/-!
# The freezing calendar on the actual block ledger

The finite calendar at a round opening acts on the same raw prefix and frozen
set as the dyadic driver. Every named monic irreducible becomes a permanent
retained factor or is one of the earlier chosen raws. The split enumeration
also places all factors of each task by a single opening.
-/

noncomputable section
namespace UnconditionalCounterexample.Variations.DyadicLedger
open RecursivePrefix Univariate Polynomial FreezingCalendar
namespace Driver
variable (D : Driver)

/-- The chronological list of raw labels and actual polynomials before a stage. -/
theorem raw_history (n : ℕ) : (D.state n).raws.reverse = (List.range n).map
    (fun j => ((D.actualRequest j).column,(chain D.requirements).raw j)) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [List.range_succ,List.map_append,D.state_succ]; simpa [Request.update] using ih

theorem frozen_iff {n : ℕ} {f : ℚ[X]} :
    f ∈ (D.state n).frozen ↔ ∃ k < n, f ∈ (D.actualRequest k).freeze := by
  induction n with
  | zero => change f ∈ (∅ : Finset ℚ[X]) ↔ _; simp
  | succ n ih =>
    rw [D.state_succ]
    change f ∈ (D.state n).frozen ∪ (D.actualRequest n).freeze ↔ _
    rw [Finset.mem_union,ih]
    constructor
    · rintro (⟨k,hk,h⟩ | h)
      · exact ⟨k,by omega,h⟩
      · exact ⟨n,by omega,h⟩
    · rintro ⟨k,hk,h⟩
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hk) with hl | rfl
      · exact Or.inl ⟨k,hl,h⟩
      · exact Or.inr h

def openingFreeze (n : ℕ) (extras : Finset ℚ[X]) : Finset ℚ[X] :=
  FreezingCalendar.pending ((chain D.requirements).approx n) (D.state n).frozen
    (FreezingCalendar.candidates (D.state n).rounds extras)

/-- Openings that follow the calendar eventually decide every horizontal. -/
theorem horizontal_decided (extra : ℕ → Finset ℚ[X])
    (hf : ∀ r, D.openingFreeze (D.opening r) (extra r) ⊆ (D.actualRequest (D.opening r)).freeze)
    (f : Horizontal) : (∃ j, (chain D.requirements).raw j = f.val) ∨
      ∃ n, f.val ∈ (D.actualRequest n).freeze ∧ f.val ∉ Set.range (chain D.requirements).raw := by
  obtain ⟨r,hr⟩ := eventually_named f
  have hc : f.val ∈ candidates r (extra r) :=
    Finset.mem_union_left _ (Finset.mem_union_left _ hr)
  let n := D.opening r
  rcases candidate_trichotomy ((chain D.requirements).approx n) (D.state n).frozen _ hc with h | ⟨j,h⟩ | h
  · obtain ⟨k,_,hk⟩ := D.frozen_iff.mp h
    exact Or.inr ⟨k,hk,D.retained k f.val hk⟩
  · exact Or.inl ⟨j.val, ((chain D.requirements).raw_agrees n j).symm.trans h⟩
  · have h' : f.val ∈ D.openingFreeze n (extra r) := by
      simpa [openingFreeze,n,D.opening_rounds] using h
    have h'' := hf r h'
    exact Or.inr ⟨n,h'',D.retained n f.val h''⟩

/-- By the end of a task's preparation stage all its nonraw horizontal
factors are in the persistent frozen set for the next round. -/
theorem split_prepared (extra : ℕ → Finset ℚ[X])
    (hf : ∀ r, D.openingFreeze (D.opening r) (extra r) ⊆ (D.actualRequest (D.opening r)).freeze)
    (x : RatFunc ℚ) (hx : x ≠ 0) (m : ℕ) (hm : 0 < m) :
    ∃ r, splitAt r = (x,⟨m,hm⟩) ∧ ∀ f : Horizontal, f.val ∣ x.num ∨ f.val ∣ x.denom →
      (∃ j < D.opening r, (chain D.requirements).raw j = f.val) ∨
        f.val ∈ (D.state (D.opening r+1)).frozen := by
  obtain ⟨r,hr,H⟩ := split_factors_requested hx m hm
  refine ⟨r,hr,?_⟩
  let n := D.opening r
  intro f hd
  rcases H ((chain D.requirements).approx n) (D.state n).frozen (extra r) f hd with h | ⟨j,h⟩ | h
  · obtain ⟨k,hk,hf'⟩ := D.frozen_iff.mp h
    exact Or.inr (D.frozen_iff.mpr ⟨k,by omega,hf'⟩)
  · exact Or.inl ⟨j.val,j.isLt,((chain D.requirements).raw_agrees n j).symm.trans h⟩
  · have h' : f.val ∈ D.openingFreeze n (extra r) := by
      simpa [openingFreeze,n,D.opening_rounds] using h
    exact Or.inr (D.frozen_iff.mpr ⟨n,Nat.lt_succ_self _,hf r h'⟩)

end Driver
end UnconditionalCounterexample.Variations.DyadicLedger
