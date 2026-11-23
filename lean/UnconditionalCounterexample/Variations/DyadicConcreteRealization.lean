import UnconditionalCounterexample.Variations.DyadicSignedMass
import UnconditionalCounterexample.Variations.DyadicAuxiliaryEmission
import UnconditionalCounterexample.Variations.DyadicConcreteDomain

/-!
# Realizing every compatible profile on the actual intersection

The retained horizontal factors and the rational primes give the coarse
profile. Actual emitted columns then fill its finite signed discrepancy.
-/

noncomputable section
namespace UnconditionalCounterexample.Variations.DyadicLedger.Calibrated
open Polynomial GuardSupport Univariate DyadicDeviations DiscreteOrders FieldGeneration
variable (a : Policy)

/-- A global lift in the rational function field for every compatible
signed profile on the calibrated geometry. -/
theorem signed_surjective (p : Profile (Aux a) (Lone a) (Horiz a))
    (h : p.MassEquations (auxIndex a) (auxSign (auxPositive a))) :
    ∃ x : (RatFunc ℚ)ˣ, signed a x = p := by
  have hbase := exists_rational_base_lift (valuation a) (signed a) (signed_values a)
    (horizontal a) (horizontal_injective a) (valuation_horizontal a) (guardPrime a)
    (guardPrime a).injective (fun i => UnivariateExtraction.guardHom (driver a).requirements (guardPrime a i))
    (valuation_guard a) p
  apply exists_of_calibrated_columns (auxIndex a) (auxSign (auxPositive a)) (signed a)
    (signed_mass a) _ _ _ p h hbase
  · intro k i
    let t := (emission a).rounds.regularStage (.balanced k i)
    refine ⟨generatorUnit (driver a) t, fun x => ?_⟩
    have he : ((driver a).actualRequest t).column = .balanced k i := (emission a).regular (.balanced k i)
    rw [generator_translates a (signed a) (signed_values a),he,columnsOfRaw_balanced]
    rfl
  · intro k i
    let t := (emission a).rounds.regularStage (.adjacent k i)
    refine ⟨generatorUnit (driver a) t, fun x => ?_⟩
    have he : ((driver a).actualRequest t).column = .adjacent k i := (emission a).regular (.adjacent k i)
    rw [generator_translates a (signed a) (signed_values a),he,columnsOfRaw_adjacent]
    rfl
  · intro k j
    obtain ⟨n,hn⟩ := auxiliary_emitted a k j
    refine ⟨generatorUnit (driver a) n, fun x => ?_⟩
    have he : ((driver a).actualRequest n).column =
        .auxiliary (auxiliaryPrime a ⟨k,j⟩) k (auxIndex a k j) (auxPositive a k j) := hn
    rw [generator_translates a (signed a) (signed_values a),he,columnsOfRaw_auxiliary]
    rfl

/-- Every nonnegative regular profile satisfying the two mass equations
is realized by an element of this very intersection of valuation rings. -/
def realization : DyadicProfiles.Realization (fullIntersection (valuation a))
    (Supplement (Aux a) (Lone a) (Horiz a)) :=
  intersectionRealization (valuation a) (signed a) (signed_values a) (auxIndex a)
    (auxSign (auxPositive a)) (signed_mass a) (signed_surjective a)

theorem realization_values (x : fullIntersection (valuation a)) (i : Coordinates a) :
    (realization a).values x i = natOrder (valuation a i) x.val :=
  intersectionRealization_values _ _ _ _ _ _ _ x i

theorem finite_extra (x : fullIntersection (valuation a)) :
    (Function.support ((realization a).extra x)).Finite :=
  intersectionRealization_finite_extra _ _ _ _ _ _ _ x

/-- The resulting rational-function domain contains a pair without a
maximal common divisor and consequently fails both chain properties. -/
theorem domain_pair_obstruction :
    (∃ x y : domain (driver a).requirements, x ≠ 0 ∧ y ≠ 0 ∧
      ∀ d, d ∣ x → d ∣ y → ∃ u, ¬ IsUnit u ∧ d*u ∣ x ∧ d*u ∣ y) ∧
      ¬ Factorization.IsStronglyAtomicDomain (domain (driver a).requirements) ∧
      ¬ Factorization.IsWeakACCP (domain (driver a).requirements) := by
  classical
  rw [domain_eq_intersection]
  let D := realization a
  exact ⟨⟨D.pairEntry false,D.pairEntry true,(D.pairEntry_spec false).1,(D.pairEntry_spec true).1,
    fun _ => D.pair_extension⟩,D.pair_obstruction.2⟩

end UnconditionalCounterexample.Variations.DyadicLedger.Calibrated
