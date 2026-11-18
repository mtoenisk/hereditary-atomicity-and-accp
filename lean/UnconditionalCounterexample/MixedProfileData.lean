import UnconditionalCounterexample.MixedGeneratorProfiles
import UnconditionalCounterexample.SparseProfileData

/-!
# Actual profile data for every infinite selected prime set

Every field is supplied by the same mixed polynomial/guard recursion. The
bundle contains elementary raw data and generator evaluations, not an ideal
realization, principal relation, or ring-property conclusion.
-/

noncomputable section
namespace UnconditionalCounterexample.MixedConstruction
open Polynomial GuardSupport
variable (S : Set PrimeIndex) (hS : S.Infinite)

/-- The elementary realized data of the one construction selected for S. -/
def profileData : SparseProfileData.Data where
  raw := raw S hS
  exponent := exponent S hS
  places := places S hS
  monic_irreducible i := ⟨(construction S hS).chain.raw_monic i,
    (construction S hS).chain.raw_irreducible i⟩
  raw_injective := fun _ _ h =>
    (construction S hS).chain.raw_degree_strict.injective (congrArg natDegree h)
  constant_ne_zero := (construction S hS).chain.raw_constant_ne_zero
  columns := MixedGeneratorProfiles.generatorProfiles S hS
  first := SparsePrimaryDomain.ofSelected_primary_zero S hS _ _
  guard_unit := (construction S hS).chain.guardChain.value_unit
  guardSupport := guardSupport S hS

@[simp] theorem profileData_domain : (profileData S hS).domain = domain S hS := rfl

end UnconditionalCounterexample.MixedConstruction
