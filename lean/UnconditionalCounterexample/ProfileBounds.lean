import UnconditionalCounterexample.ValuationProfiles
import Mathlib.Data.Finset.Lattice.Fold

/-!
# Uniform bounds on all coordinates of an element

Eventual constancy on primary coordinates and finite outside support give a
single natural bound on every coordinate of a fixed nonzero element. This
supplies the bound required by the arbitrary-ideal SP factorization argument.
-/

namespace UnconditionalCounterexample.ValuationProfiles
variable {R ι : Type*} [CommRing R] [IsDomain R]

/-- The complete profile of one nonzero element is uniformly bounded. -/
theorem exists_all_coordinate_bound (v : ValuationProfiles R ι) (x : R) (hx : x ≠ 0) :
    ∃ N : ℕ, ∀ p, v.value p x ≤ N := by
  classical
  obtain ⟨M, hM⟩ := v.eventually_primary x hx
  let outside := (v.finite_outside x hx).toFinset
  let P := (Finset.range M).sup (fun j => v.value (.primary j) x)
  let Q := outside.sup (fun i => v.value (.outside i) x)
  refine ⟨max (v.value .limit x) (max P Q), ?_⟩
  intro p
  cases p with
  | limit => exact le_max_left _ _
  | primary j =>
    by_cases hj : j < M
    · exact (Finset.le_sup (f := fun j => v.value (.primary j) x) (Finset.mem_range.mpr hj)).trans
        ((le_max_left P Q).trans (le_max_right _ _))
    · rw [hM j (Nat.le_of_not_gt hj)]
      exact le_max_left _ _
  | outside i =>
    by_cases hi : i ∈ outside
    · exact (Finset.le_sup (f := fun i => v.value (.outside i) x) hi).trans
        ((le_max_right P Q).trans (le_max_right _ _))
    · have hz : v.value (.outside i) x = 0 := by simpa [outside] using hi
      rw [hz]
      exact Nat.zero_le _

end UnconditionalCounterexample.ValuationProfiles
