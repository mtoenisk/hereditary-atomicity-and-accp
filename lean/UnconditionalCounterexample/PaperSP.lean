import UnconditionalCounterexample.PaperIdealRealization
import UnconditionalCounterexample.PaperThresholdIdeals
import UnconditionalCounterexample.PaperTargets

/-!
# The actual counterexample is an SP-domain

Every positive threshold profile is realized by an invertible fractional ideal.
Nonnegative coordinates make it an ordinary ideal, and the actual maximal-order
dictionary identifies its localized threshold ideals. The arbitrary-ideal
argument then yields a finite product of radical ideals, expressed here as the
literal list-valued paper target.
-/

noncomputable section
namespace UnconditionalCounterexample.PaperConstruction
open PicardProfiles FractionalIdealProfiles

/-- Every ideal of the fixed paper domain is a finite product of actual radical
ideals. This also includes zero and the unit ideal. -/
theorem exists_radical_ideal_list (I : Ideal domain) :
    ∃ L : List (Ideal domain), (∀ J ∈ L, J.IsRadical) ∧ L.prod = I := by
  have hrealize : ∀ (x : domain) (hx : x ≠ 0) (k : ℕ) (hk : 0 < k),
      ∃ J : PaperIdealProfiles.Fractional,
        HasProfile PaperIdealProfiles.v J (coordinate (thresholdProfile x hx k hk)) := by
    intro x hx k hk
    obtain ⟨J, hJ⟩ := PaperIdealProfiles.exists_invertible_profile (thresholdProfile x hx k hk)
    exact ⟨J.val, hJ⟩
  obtain ⟨N, K, hK, hI⟩ :=
    PaperThresholdIdeals.radical_products_of_threshold_realizations hrealize I
  refine ⟨(List.range N).map K, ?_, ?_⟩
  · intro J hJ
    obtain ⟨k, _, rfl⟩ := List.mem_map.mp hJ
    exact hK k
  · rw [← List.prod_toFinset K (List.nodup_range (n := N))]
    simpa only [List.toFinset_range] using hI.symm

/-- The fixed paper construction satisfies the exact SP-domain target. -/
theorem isSPDomain : PaperTargets.IsSPDomain domain := by
  intro I _ _
  exact exists_radical_ideal_list I

end UnconditionalCounterexample.PaperConstruction
