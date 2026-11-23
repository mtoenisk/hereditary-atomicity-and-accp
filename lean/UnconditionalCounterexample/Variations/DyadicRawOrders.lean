import UnconditionalCounterexample.Variations.DyadicCalibratedSites
import UnconditionalCounterexample.Variations.DyadicLedgerValues

/-!
# Birth-independent orders of selected dyadic raws

Each round allocates every regular fibre touched by one of its columns
before selecting that column. An auxiliary raw uses its own prime already
allocated at the opening. Consequently the conditional order formula for
a later birth agrees everywhere with the ledger's untruncated integer row.
-/

noncomputable section
namespace UnconditionalCounterexample.Variations.DyadicLedger

open GuardSupport Univariate MixedStageSelection DyadicBlocks

theorem Driver.generator_primary_order_of_coverage (D : Driver) (n : ℕ) (p : PrimeIndex) (r : FibreRole)
    (hr : D.permanentRole p = some r)
    (hc : (D.actualRequest n).column.atPrimary p (some r) ≠ 0 → p ∈ D.assigned (n+1)) :
    ((permanentSite D.requirements p).evaluate false
      (Or.inr ((D.paired_iff_role p).mpr (by simp [hr]))) ((chain D.requirements).generators n)).valuation =
      (D.actualRequest n).column.atPrimary p (some r) := by
  obtain ⟨birth,hp,he⟩ := (D.permanentRole_iff p r).mp hr
  have hpairs := ((D.actualRequest birth).paired p hp).mpr (by simp [he])
  rw [D.generator_primary_order n birth p hp hpairs,he]
  split_ifs with hn
  · by_contra hne
    exact (D.actualRequest birth).births.fresh p hp (assigned_mono D.requirements hn (hc (Ne.symm hne)))
  · rfl

namespace Calibrated

variable (a : Policy)

private theorem stage_in_block (n : ℕ) :
    ∃ r, (driver a).opening r ≤ n ∧
      ((driver a).actualRequest n).column ∈ ((emission a).block r).columns := by
  let E := emission a
  let r := locate E.rounds.length_pos n
  obtain ⟨hlo,hhi⟩ := locate_bounds E.rounds.length_pos n
  change boundary E.rounds.length r ≤ n at hlo
  change n < boundary E.rounds.length r + E.rounds.length r at hhi
  rw [E.stage_boundary] at hlo hhi
  have hlen : E.rounds.length r = (E.block r).columns.length := by
    rw [Block.length_columns]; rfl
  rw [hlen] at hhi
  change (driver a).opening r ≤ n at hlo
  change n < (driver a).opening r + (E.block r).columns.length at hhi
  let j := n - (driver a).opening r
  have hj : j < (E.block r).columns.length := by dsimp [j]; omega
  have he := (driver a).opening_emits (r := r) (i := j) (c := (E.block r).columns[j])
    (by rw [E.opened]; exact List.getElem?_eq_getElem hj)
  rw [Nat.add_sub_of_le hlo] at he
  refine ⟨r,hlo,?_⟩
  rw [he]
  exact List.getElem_mem hj

private theorem regular_assigned (n : ℕ) (l : RegularLabel)
    (h : l ∈ ((driver a).actualRequest n).column.regularSupport) :
    regularPrime a l ∈ (driver a).assigned (n+1) := by
  obtain ⟨r,hle,hc⟩ := stage_in_block a n
  let t := (driver a).opening r
  let D := driver a
  have he : l ∈ (actualLayout a t).block.required :=
    Finset.mem_biUnion.mpr ⟨(D.actualRequest n).column,List.mem_toFinset.mpr hc,h⟩
  rcases (actualRoom a t).coverage l he with ⟨p,hr⟩ | ⟨p,hp,hr⟩
  · have ha : p ∈ D.assigned t := by
      by_contra hn
      rw [D.role_none_of_unassigned t p hn] at hr
      contradiction
    have hperm := (D.role_eq_permanent p ha).symm.trans hr
    have hprime := (regular_exists_unique a l).unique (regularPrime_role a l) hperm
    exact hprime ▸ assigned_mono D.requirements (by dsimp [t]; omega : t ≤ n+1) ha
  · obtain ⟨hm,he',_⟩ := (installed a t (D.opening_empty r)).included p hp
    have hperm := (D.permanentRole_requested p hm).trans (he'.trans hr)
    have hprime := (regular_exists_unique a l).unique (regularPrime_role a l) hperm
    rw [hprime]
    apply assigned_mono D.requirements (Nat.succ_le_succ hle)
    exact (selection D.requirements t).batch.processed_subset_assigned (D.schedule.requested_processed t hm)

private theorem auxiliary_assigned (n : ℕ) (p : PrimeIndex) (k : Bool) (i : ℕ) (e : Bool)
    (h : ((driver a).actualRequest n).column = .auxiliary p k i e) : p ∈ (driver a).assigned (n+1) := by
  let D := driver a
  let E := emission a
  rcases E.exhaustive n with ⟨r,j,hn,hc⟩ | ⟨g,_,hg⟩
  · obtain ⟨q,l,t,f,hq,he,_⟩ := (recorded a).allocated r (E.block r).auxiliary[j.val]
      (List.getElem_mem j.isLt)
    rw [he,h] at hc
    cases hc
    have hle : D.opening r ≤ n := by
      rw [← hn, ← E.stage_boundary]
      exact Nat.le_add_right _ _
    apply assigned_mono D.requirements (Nat.succ_le_succ hle)
    exact (selection D.requirements (D.opening r)).batch.processed_subset_assigned
      (D.schedule.requested_processed _ hq)
  · rw [h] at hg
    cases g <;> cases hg

/-- Every nonzero prescribed primary order is already supported at the stage
of the raw, whether it is an old site or was born at this opening. -/
theorem generator_primary_order (n : ℕ) (p : PrimeIndex) (r : FibreRole)
    (hr : (driver a).permanentRole p = some r) :
    ((permanentSite (driver a).requirements p).evaluate false
      (Or.inr (((driver a).paired_iff_role p).mpr (by simp [hr])))
      ((chain (driver a).requirements).generators n)).valuation =
      ((driver a).actualRequest n).column.atPrimary p (some r) := by
  apply (driver a).generator_primary_order_of_coverage n p r hr
  intro h
  cases r with
  | regular c k j =>
    have hprime := (regular_exists_unique a (c,k,j)).unique hr (regularPrime_role a (c,k,j))
    exact hprime ▸ regular_assigned a n (c,k,j) (((driver a).actualRequest n).column.supports_nonzero p (c,k,j) h)
  | auxiliary k j e =>
    cases hc : ((driver a).actualRequest n).column with
    | balanced l t | adjacent l t => simp [hc,RawColumn.atPrimary] at h
    | auxiliary q l t b =>
      have hpq : p = q := by by_contra! hn; simp [hc,RawColumn.atPrimary,hn] at h
      exact hpq ▸ auxiliary_assigned a n q l t b hc

end Calibrated
end UnconditionalCounterexample.Variations.DyadicLedger
