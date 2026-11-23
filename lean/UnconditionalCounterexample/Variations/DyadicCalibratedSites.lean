import UnconditionalCounterexample.Variations.DyadicCalibratedDriver
import UnconditionalCounterexample.Variations.DyadicDispatchEmission

/-!
# Exact column indexing and permanent regular primes

The support of every balanced column in its actual finite block contains both
centre labels at that index. Every required label therefore has exactly one
permanent prime. The emitted raw labels are injective across the entire run.
-/

noncomputable section
namespace UnconditionalCounterexample.Variations.DyadicLedger
open GuardSupport RecursivePrefix Univariate DyadicBlocks

private theorem Block.balanced_mem (s : Block) (k : Bool) {j : ℕ} (hj : j < s.width) :
    RawColumn.balanced k (s.start+j) ∈ s.columns := by
  let t := Rounds.code k j
  have ht : t < 2*s.width := by cases k <;> simp [t,Rounds.code] <;> omega
  have hlast : 2*s.width-1 < 2*s.width := by have := s.positive; omega
  have h : s.perm t < 2*s.width := by
    unfold Block.perm
    by_cases hr : t = s.reserved.val
    · rw [hr,Equiv.swap_apply_left]; exact hlast
    by_cases hl : t = 2*s.width-1
    · rw [hl,Equiv.swap_apply_right]; exact s.reserved.isLt
    rwa [Equiv.swap_apply_of_ne_of_ne hr hl]
  apply List.mem_append_right
  refine List.mem_map.mpr ⟨s.perm t,List.mem_range.mpr h,?_⟩
  simp only [Block.perm,Equiv.swap_apply_self]
  simpa [t] using s.localColumn_code true k j

namespace Calibrated
variable (a : Policy)

abbrev emission := dispatcherEmission (planner a)

theorem recorded : (emission a).Recorded where
  nodup r := by
    let n := (driver a).opening r
    change (actualLayout a n).block.auxiliary.Nodup
    rw [(actualLayout a n).auxiliary_eq]
    exact OpeningCalibration.columns_nodup _
  allocated r c hc := by
    let D := driver a
    let n := D.opening r
    change c ∈ (actualLayout a n).block.auxiliary at hc
    rw [(actualLayout a n).auxiliary_eq] at hc
    obtain ⟨p,k,i,e,hr,he⟩ := (OpeningCalibration.mem_columns _ c).mp hc
    have has : RawColumn.auxiliary p.val k i e ∈ OpeningCalibration.columns
        (phase (D.state n) ((chain D.requirements).approx n) (table D.requirements n)) := he ▸ hc
    obtain ⟨hp,hu⟩ := ((actualRoom a n).auxiliary_iff _ (installed a n (D.opening_empty r))
      p.val k i e).mpr has
    exact ⟨p.val,k,i,e,hp,he,hu⟩

theorem column_injective : Function.Injective (fun n => ((driver a).actualRequest n).column) :=
  (emission a).column_injective (recorded a)

/-- Literal permanent primes attached to every regular primary index. -/
theorem regular_exists_unique (l : RegularLabel) : ∃! p, (driver a).permanentRole p = some l.role := by
  rcases l with ⟨c,k,i⟩
  let D := driver a
  let E := emission a
  let r := locate E.rounds.width_pos i
  let s := E.block r
  obtain ⟨hlo,hhi⟩ := locate_bounds E.rounds.width_pos i
  change boundary E.rounds.width r ≤ i at hlo
  change i < boundary E.rounds.width r + s.width at hhi
  rw [E.index_boundary r] at hlo hhi
  have hi : i - s.start < s.width := by change s.start ≤ i at hlo; change i < s.start+s.width at hhi; omega
  have hh := s.balanced_mem k hi
  have hj : s.start + (i-s.start) = i := Nat.add_sub_of_le hlo
  rw [hj] at hh
  apply regular_covered a (D.opening r) (D.opening_empty r)
  apply Finset.mem_biUnion.mpr
  refine ⟨RawColumn.balanced k i,List.mem_toFinset.mpr hh,?_⟩
  cases c <;> simp [RawColumn.regularSupport]

def regularPrime (l : RegularLabel) : PrimeIndex := (regular_exists_unique a l).exists.choose

theorem regularPrime_role (l : RegularLabel) : (driver a).permanentRole (regularPrime a l) = some l.role :=
  (regular_exists_unique a l).exists.choose_spec

theorem regularPrime_injective : Function.Injective (regularPrime a) := by
  rintro ⟨c,k,i⟩ ⟨d,l,j⟩ h
  have h₁ := regularPrime_role a (c,k,i)
  rw [h,regularPrime_role] at h₁
  cases h₁
  rfl

end Calibrated
end UnconditionalCounterexample.Variations.DyadicLedger
