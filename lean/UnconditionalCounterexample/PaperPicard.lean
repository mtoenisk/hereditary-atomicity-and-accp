import UnconditionalCounterexample.PrincipalProfileImage
import UnconditionalCounterexample.PaperIdealRealization
import UnconditionalCounterexample.ClassPicBridge
import UnconditionalCounterexample.PaperTargets

noncomputable section
namespace UnconditionalCounterexample.PaperPicard
open PaperConstruction

local instance : IsFractionRing domain (RatFunc ℚ) := fractionRing

/-- Compatibility on actual nonzero principal fractional ideals identifies
exactly the relation subgroup, rather than only one containment. -/
theorem principalProfiles_eq_of_agrees
    (e : Additive PaperIdealProfiles.Fractionalˣ ≃+ PrincipalProfileImage.Group)
    (he : ∀ u : (RatFunc ℚ)ˣ,
      e (Additive.ofMul (toPrincipalIdeal domain (RatFunc ℚ) u)) =
        PrincipalProfileImage.profile (Additive.ofMul u)) :
    ClassPicBridge.principalProfiles domain (RatFunc ℚ) e =
      PrincipalProfileImage.principals := by
  ext x
  rw [ClassPicBridge.mem_principalProfiles_iff, PrincipalProfileImage.mem_principals_iff]
  simp only [he]

/-- The ideal-profile equivalence carries actual principal ideals to precisely
the subgroup already computed from actual rational functions. -/
theorem principalProfiles_eq :
    ClassPicBridge.principalProfiles domain (RatFunc ℚ) PaperIdealProfiles.profileEquiv =
      PrincipalProfileImage.principals := by
  apply principalProfiles_eq_of_agrees
  intro u
  exact PaperIdealProfiles.principal_profile_eq u

/-- The actual invertible-fractional-ideal class group of the constructed
ring is the countable direct sum of cyclic groups of order three. -/
def classGroupEquiv : Additive (ClassGroup domain) ≃+ (ℕ →₀ ZMod 3) :=
  (ClassPicBridge.classGroupEquivQuotientOfEq domain (RatFunc ℚ)
    PaperIdealProfiles.profileEquiv PrincipalProfileImage.principals principalProfiles_eq).trans
      PrincipalProfileImage.quotientEquiv

/-- The same unconditional result for mathlib's actual Picard group. -/
def picardEquiv : Additive (CommRing.Pic domain) ≃+ (ℕ →₀ ZMod 3) :=
  (ClassPicBridge.picardEquivQuotientOfEq domain (RatFunc ℚ)
    PaperIdealProfiles.profileEquiv PrincipalProfileImage.principals principalProfiles_eq).trans
      PrincipalProfileImage.quotientEquiv

theorem classGroupConclusion : PaperTargets.ClassGroupConclusion domain := ⟨classGroupEquiv⟩

theorem picardGroupConclusion : PaperTargets.PicardGroupConclusion domain := ⟨picardEquiv⟩

end UnconditionalCounterexample.PaperPicard
