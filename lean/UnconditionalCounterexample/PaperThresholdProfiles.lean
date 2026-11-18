import UnconditionalCounterexample.PaperAtoms
import UnconditionalCounterexample.PicardProfiles

/-!
# Actual positive valuation-level profiles

For each nonzero element of the fixed constructed domain and every positive
level, its valuation-level indicator is a nonnegative restricted integer
profile. The finite tuple is provided by the actual PicardProfiles constructor.
The ideal realizing this profile is supplied separately.
-/

noncomputable section
namespace UnconditionalCounterexample.PaperConstruction
open CompleteProfiles PicardProfiles

/-- The literal indicator of a positive valuation level of the actual element. -/
def thresholdCoordinates (x : domain) (k : ℕ) : ProfilePlace (Outside poles) → ℤ :=
  fun p => if k ≤ valuationProfiles.value p x then 1 else 0

/-- The eventual primary value and finite outside support are preserved by
positive-level indicators, including the actual E value. -/
theorem thresholdCoordinates_restricted (x : domain) (hx : x ≠ 0) (k : ℕ) (hk : 0 < k) :
    Restricted (thresholdCoordinates x k) := by
  obtain ⟨N, hN⟩ := valuationProfiles.eventually_primary x hx
  refine ⟨⟨N, fun j hj => ?_⟩, ?_⟩
  · simp only [thresholdCoordinates, hN j hj]
  · apply (valuationProfiles.finite_outside x hx).subset
    intro i hi hz
    apply hi
    simp [thresholdCoordinates, hz, Nat.not_le_of_gt hk]

/-- The actual finite representation of this positive level indicator. -/
def thresholdProfile (x : domain) (hx : x ≠ 0) (k : ℕ) (hk : 0 < k) : Profile (Outside poles) :=
  ofCoordinates (thresholdCoordinates x k) (thresholdCoordinates_restricted x hx k hk)

@[simp] theorem thresholdProfile_coordinate (x : domain) (hx : x ≠ 0) (k : ℕ) (hk : 0 < k)
    (p : ProfilePlace (Outside poles)) :
    coordinate (thresholdProfile x hx k hk) p =
      if k ≤ valuationProfiles.value p x then 1 else 0 := by
  simp only [thresholdProfile, coordinate_ofCoordinates, thresholdCoordinates]

/-- Every coordinate of the actual threshold tuple is integral and nonnegative. -/
theorem thresholdProfile_nonneg (x : domain) (hx : x ≠ 0) (k : ℕ) (hk : 0 < k)
    (p : ProfilePlace (Outside poles)) : 0 ≤ coordinate (thresholdProfile x hx k hk) p := by
  rw [thresholdProfile_coordinate]
  split_ifs <;> norm_num

end UnconditionalCounterexample.PaperConstruction
