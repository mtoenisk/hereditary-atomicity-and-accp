import UnconditionalCounterexample.SparseIdealRealization
import UnconditionalCounterexample.SparsePrincipalProfiles
import UnconditionalCounterexample.ClassPicBridge
import UnconditionalCounterexample.PaperTargets

noncomputable section
namespace UnconditionalCounterexample.SparsePicard

variable (A : SparseProfileData.Data)
local instance : IsFractionRing A.domain (RatFunc ℚ) := A.fractionRing

/-- The actual ideal-profile equivalence identifies exactly the actual
principal subgroup of rational functions. -/
theorem principalProfiles_eq :
    ClassPicBridge.principalProfiles A.domain (RatFunc ℚ) (SparseIdealProfiles.profileEquiv A) =
      SparsePrincipalProfiles.principals A := by
  ext x
  rw [ClassPicBridge.mem_principalProfiles_iff, SparsePrincipalProfiles.mem_principals_iff]
  simp only [SparseIdealProfiles.profileEquiv_apply, SparseIdealProfiles.principal_profile_eq]

/-- The actual class group for any supplied realized sparse construction. -/
def classGroupEquiv : Additive (ClassGroup A.domain) ≃+ (ℕ →₀ ZMod 3) :=
  (ClassPicBridge.classGroupEquivQuotientOfEq A.domain (RatFunc ℚ)
    (SparseIdealProfiles.profileEquiv A) (SparsePrincipalProfiles.principals A)
      (principalProfiles_eq A)).trans (SparsePrincipalProfiles.quotientEquiv A)

/-- The actual Picard group for the same sparse intersection. -/
def picardEquiv : Additive (CommRing.Pic A.domain) ≃+ (ℕ →₀ ZMod 3) :=
  (ClassPicBridge.picardEquivQuotientOfEq A.domain (RatFunc ℚ)
    (SparseIdealProfiles.profileEquiv A) (SparsePrincipalProfiles.principals A)
      (principalProfiles_eq A)).trans (SparsePrincipalProfiles.quotientEquiv A)

theorem classGroupConclusion : PaperTargets.ClassGroupConclusion A.domain := ⟨classGroupEquiv A⟩

theorem picardGroupConclusion : PaperTargets.PicardGroupConclusion A.domain := ⟨picardEquiv A⟩

end UnconditionalCounterexample.SparsePicard
