import UnconditionalCounterexample.Variations.MultivariateSelectionExamples
import UnconditionalCounterexample.Variations.MultiDomainRealized
import UnconditionalCounterexample.Variations.DimensionOne

/-!
# Named domains in the two boundary dimensions

Both domains use the chronological selector over the rational function
field. Their dimensions and normality are intrinsic to these subrings.
-/

noncomputable section
namespace UnconditionalCounterexample.Variations

open GuardSupport MultivariateSelection MultiDomain

def ordinaryDimensionDomain (r : ℕ) : Subring (FunctionField (r+1)) := ordinary (actualData r false)

def upperDimensionDomain (r : ℕ) : Subring (FunctionField (r+1)) :=
  pullback (actualData r true) (flagPoint r) (flagPoint_retained (actualLocal r true)) reservedPrime.val

theorem ordinaryDimensionDomain_fraction (r : ℕ) : IsFractionRing (ordinaryDimensionDomain r) (FunctionField (r+1)) :=
  (actualPlaces r false).ordinary_fraction _ _

theorem upperDimensionDomain_fraction (r : ℕ) : IsFractionRing (upperDimensionDomain r) (FunctionField (r+1)) := by
  let : IsFractionRing (ordinary (actualData r true)) (FunctionField (r+1)) :=
    (actualPlaces r true).ordinary_fraction (actualRaw r true) (actualData r true).raw_ne
  exact pullback_fractionRing (actualData r true) _ _ _

theorem ordinaryDimensionDomain_normal (r : ℕ) : IsIntegrallyClosed (ordinaryDimensionDomain r) := by
  let : IsFractionRing (ordinary (actualData r false)) (FunctionField (r+1)) := ordinaryDimensionDomain_fraction r
  exact ordinary_normal (actualData r false)

theorem upperDimensionDomain_normal (r : ℕ) : IsIntegrallyClosed (upperDimensionDomain r) := by
  let : IsFractionRing (ordinary (actualData r true)) (FunctionField (r+1)) :=
    (actualPlaces r true).ordinary_fraction (actualRaw r true) (actualData r true).raw_ne
  exact pullback_normal (actualData r true) _ _ _

theorem ordinaryDimensionDomain_dimension (r : ℕ) :
    ringKrullDim (ordinaryDimensionDomain r) = (r+1 : ℕ) := by
  let L := actualLocal r false
  let G := standardGeometry r
  apply (places L G).ordinary_dimension_of_profiles (siteRaw L G) _ (flagPoint r) (flagPoint_retained L)
    (realizedProfiles reservedPrime false) (selectedClearing L G (raw_not_divisible_first L)) (places L G).injective
  intro p
  exact finite_witt_residue p.val (GaloisField p.val (permanentFibre L G p).guard.degree)

theorem upperDimensionDomain_dimension (r : ℕ) : ringKrullDim (upperDimensionDomain r) = (r+2 : ℕ) :=
  pullback_dimension (A := selectedData (actualLocal r true) (standardGeometry r)) (flagPoint r)
    (flagPoint_retained (actualLocal r true)) (selectedClearing (actualLocal r true) (standardGeometry r)
      (raw_not_divisible_first (actualLocal r true))) reservedPrime.val

theorem ordinaryDimensionDomain_chain (r : ℕ) : ∃ t : ordinaryDimensionDomain r,
    (t : FunctionField (r+1)) = coordinate 0 ∧ HasStrictChainAt (t^3) := by
  let C := realizedChoices (r := r) reservedPrime false
  exact ⟨C.parameter, rfl, C.ordinary_chain⟩

theorem not_wf_of_strict_chain {D : Type*} [CommRing D] [IsDomain D] {a : D} (h : HasStrictChainAt a) :
    ¬ WfDvdMonoid D := by
  obtain ⟨x,_,_,hx⟩ := h
  exact Factorization.not_wfDvdMonoid_iff_exists_strictMono_principalIdealChain.mpr
    ⟨fun n ↦ Ideal.span ({x n} : Set D),fun n ↦ ⟨x n,rfl⟩,hx⟩

end UnconditionalCounterexample.Variations
