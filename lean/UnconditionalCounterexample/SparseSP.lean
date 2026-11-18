import UnconditionalCounterexample.SparseIdealRealization
import UnconditionalCounterexample.SparseStalkOrders
import UnconditionalCounterexample.ProfileSP

/-!
# SP factorization for the actual sparse-primary domain

The sparse construction supplies the literal full valuation intersection,
normalized orders at every maximal ideal and realization of every restricted
fractional-ideal profile. The generic arbitrary-ideal argument therefore
applies with no finite-generation assumption on the ideal being factored.
-/

noncomputable section
namespace UnconditionalCounterexample.SparseSP
open WithZero SparseProfileData PicardProfiles FractionalIdealProfiles
open RadicalIdealProducts
open scoped nonZeroDivisors
variable (A : Data)
local instance : IsFractionRing A.domain (RatFunc ℚ) := A.fractionRing

/-- The actual maximal label has precisely the natural order in the complete
sparse profile family. -/
theorem value_at_maximal (M : SparseMaximalSpectrum.Maximal A)
    (x : A.domain) (hx : x ≠ 0) :
    SparseIdealProfiles.v A ((SparseMaximalSpectrum.labelEquivMaximal A).symm M)
      (algebraMap A.domain (RatFunc ℚ) x) =
      exp (-(A.profiles.value ((SparseMaximalSpectrum.labelEquivMaximal A).symm M) x : ℤ)) := by
  change A.valuations ((SparseMaximalSpectrum.labelEquivMaximal A).symm M) (x : RatFunc ℚ) = _
  rw [DiscreteOrders.value_eq_exp_neg_order _ (fun h => hx (Subtype.ext h)),
    ← A.profiles_cast _ x hx]

/-- Every ideal of the actual sparse domain is a finite product of actual
radical ideals, including zero and the unit ideal. -/
theorem exists_radical_ideal_list (I : Ideal A.domain) :
    ∃ L : List (Ideal A.domain), (∀ J ∈ L, J.IsRadical) ∧ L.prod = I := by
  apply ProfileSP.exists_radical_ideal_list A.profiles (SparseIdealProfiles.v A)
    (SparseIdealProfiles.full A) (SparseMaximalSpectrum.labelEquivMaximal A).symm
    (value_at_maximal A) _ _ I
  · intro M x hx
    exact SparseMaximalSpectrum.principal_power A M x hx
  · intro f
    obtain ⟨J, hJ⟩ := SparseIdealProfiles.exists_invertible_profile A f
    exact ⟨J.val, hJ⟩

/-- The exact SP-domain predicate for the actual sparse-primary domain. -/
theorem isSPDomain : PaperTargets.IsSPDomain A.domain := by
  intro I _ _
  exact exists_radical_ideal_list A I

end UnconditionalCounterexample.SparseSP
