import UnconditionalCounterexample.MixedProfileData
import UnconditionalCounterexample.SparseSP

/-!
# The selected-prime construction is an SP-domain

For every infinite selected prime set, the single actual recursive construction
satisfies the arbitrary-ideal radical factorization property. The witness is
the original subring of the rational function field, with no remaining
realization or spectrum hypotheses.
-/

noncomputable section
namespace UnconditionalCounterexample.MixedConstruction
open GuardSupport
variable (S : Set PrimeIndex) (hS : S.Infinite)

/-- Every actual maximal localization is a discrete valuation ring. -/
theorem isAlmostDedekindDomain : IsAlmostDedekindDomain (domain S hS) :=
  SparseSpectrum.every_maximal_stalk_isDVR (raw S hS) (exponent S hS) (places S hS)
    (profileData S hS).columns.b (profileData S hS).columns.q (profileData S hS).columns.guard
    (profileData S hS).constant_ne_zero (guardSupport S hS)

/-- Every ordinary ideal of the selected-prime domain has a finite list of
actual radical factors. -/
theorem exists_radical_ideal_list (I : Ideal (domain S hS)) :
    ∃ L : List (Ideal (domain S hS)), (∀ J ∈ L, J.IsRadical) ∧ L.prod = I :=
  SparseSP.exists_radical_ideal_list (profileData S hS) I

/-- The exact SP-domain target for each infinite selected prime set. -/
theorem isSPDomain : PaperTargets.IsSPDomain (domain S hS) :=
  SparseSP.isSPDomain (profileData S hS)

end UnconditionalCounterexample.MixedConstruction
