import Factorization.Hierarchy
import Factorization.LengthSets
import Mathlib.RingTheory.UniqueFactorizationDomain.Basic
import Mathlib.Algebra.Field.Basic

/-!
# Basic sources of bounded factorization

The field conclusion concerns intrinsic field factorizations. It does not
assert that arbitrary subrings of a field have bounded factorization.
-/

namespace Factorization

universe u

/-- A unit has only the empty factorization into nonunits. -/
theorem hasBoundedFactorizations_of_isUnit {M : Type u} [CommMonoid M]
    {x : M} (hx : IsUnit x) : HasBoundedFactorizations x := by
  refine ⟨0, fun s hs hprod => ?_⟩
  have hempty : s = 0 := by
    apply Multiset.eq_zero_of_forall_notMem
    intro a ha
    exact hs a ha (isUnit_of_dvd_unit (Multiset.dvd_prod ha) (hprod.isUnit_iff.mpr hx))
  simp only [hempty, Multiset.card_zero, le_refl]

/-- Every field has bounded factorizations in its own multiplicative monoid. -/
theorem isBFDomain_of_field (K : Type u) [Field K] : IsBFDomain K :=
  fun _ hx => hasBoundedFactorizations_of_isUnit (isUnit_iff_ne_zero.mpr hx)

/-- Unique irreducible factorizations bound all nonunit factorizations. -/
theorem hasBoundedFactorizations_of_uniqueFactorizationMonoid
    {M : Type u} [CommMonoidWithZero M] [UniqueFactorizationMonoid M]
    {x : M} (hx : x ≠ 0) : HasBoundedFactorizations x := by
  obtain ⟨f, hf, hfx⟩ := WfDvdMonoid.exists_factors x hx
  refine ⟨f.card, fun s hs hprod => ?_⟩
  obtain ⟨t, ht, hts, hcard⟩ := exists_irreducible_refinement s hs
    (fun p hp => WfDvdMonoid.exists_factors p
      (ne_zero_of_dvd_ne_zero hx ((Multiset.dvd_prod hp).trans hprod.dvd)))
  have hrel : Multiset.Rel Associated t f :=
    UniqueFactorizationMonoid.factors_unique ht hf (hts.trans (hprod.trans hfx.symm))
  exact hcard.trans_eq (Multiset.card_eq_card_of_rel hrel)

/-- A unique factorization domain is a bounded factorization domain. -/
theorem isBFDomain_of_uniqueFactorizationMonoid
    (R : Type u) [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R] :
    IsBFDomain R :=
  fun _ hx => hasBoundedFactorizations_of_uniqueFactorizationMonoid hx

end Factorization
