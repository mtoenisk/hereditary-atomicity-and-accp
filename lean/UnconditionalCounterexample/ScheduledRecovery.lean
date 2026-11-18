import UnconditionalCounterexample.GeometricReservations
import UnconditionalCounterexample.StageExponents
import UnconditionalCounterexample.WordGeometry

/-!
# Actual stage-list geometry recovers the rational hull

The finite reservation tests are imposed before any subring or unbounded
decomposition is considered. This theorem pulls their eventual all-word
conclusions back along one actual escaping stage sequence, then applies the
literal old-product WordGeometry theorem. Exact universal fraction identities,
positive old exponents, degree inequalities and successful finite tests are the
explicit constructor obligations; no eventual geometric recovery is assumed.
-/

namespace UnconditionalCounterexample.ScheduledRecovery

open Polynomial Filter RawWords

/-- The exact normalized generators in the raw polynomial construction. -/
noncomputable def generators (F : ℕ → ℚ[X]) (E : ℕ → ℕ) : ℕ → RatFunc ℚ :=
  normalizedFactor (fun j => algebraMap ℚ[X] (RatFunc ℚ) (F j)) E

/-- A single actual escaping sequence chosen from the finite stage lists
recovers the rational hull from the concrete reservation/test schedule. -/
theorem hull_eq_top_of_listed_sequence
    (K : Type) [Field K] [Algebra ℚ K] [IsAlgClosed K]
    (enumeration : ℕ → K) (henum : Function.Surjective enumeration)
    (F : ℕ → ℚ[X]) (E : ℕ → ℕ)
    (hF : ∀ n, Irreducible (F n)) (hdegreeF : StrictMono (fun n => (F n).natDegree))
    (d : ∀ n, StageWord n (n + 1) → ℕ → ℕ)
    (hd : ∀ n w j, j < n → 0 < d n w j)
    (hfrac : ∀ n (w : StageWord n (n + 1)),
      generators F E n ^ w.latestExponent *
        (∏ j ∈ Finset.range n, generators F E j ^ w.oldExponent j) =
      (algebraMap ℚ[X] (RatFunc ℚ) (F n)) ^ w.latestExponent /
        algebraMap ℚ[X] (RatFunc ℚ) (WordGeometry.oldDenominator F n (d n w)))
    (hdegree : ∀ n (w : StageWord n (n + 1)),
      (WordGeometry.oldDenominator F n (d n w)).natDegree < w.latestExponent * (F n).natDegree)
    (htests : ∀ n t,
      t ∈ GeometricReservations.finiteTests (GeometricReservations.reservedPoints enumeration F n)
        (fun w : StageWord n (n + 1) => w.latestExponent)
        (fun w => (WordGeometry.oldDenominator F n (d n w)).map (algebraMap ℚ K)) →
      SeparationExclusions.Test.Holds ((F n).map (algebraMap ℚ K)) t)
    (α₀ : K) (hα₀ : ∀ j, (F j).eval₂ (algebraMap ℚ K) α₀ ≠ 0)
    (T : Subring (PoleAlgebra.generated (Set.range F)))
    (y : ℕ → T) (stage : ℕ → ℕ) (hstage : Tendsto stage atTop atTop)
    (w : ∀ i, StageWord (stage i) (stage i + 1))
    (hword : ∀ i, ((y i : PoleAlgebra.generated (Set.range F)) : RatFunc ℚ) =
      generators F E (stage i) ^ (w i).latestExponent *
        (∏ j ∈ Finset.range (stage i), generators F E j ^ (w i).oldExponent j)) :
    RationalHull.hull T = ⊤ := by
  apply WordGeometry.hull_eq_top_of_escaping_raw_words K F hF hdegreeF α₀ hα₀ T y stage hstage
    (fun i => (w i).latestExponent) (fun i => (w i).latestExponent_bounds.1)
    (fun i => d (stage i) (w i)) (fun i => hd (stage i) (w i))
  · intro i
    exact (hword i).trans (hfrac (stage i) (w i))
  · exact Filter.Eventually.of_forall (fun i => hdegree (stage i) (w i))
  · intro α β hα hβ hne
    have hevent := GeometricReservations.eventually_pair_tests enumeration henum F
      (fun n => StageWord n (n + 1))
      (fun _ w => w.latestExponent)
      (fun n w => (WordGeometry.oldDenominator F n (d n w)).map (algebraMap ℚ K))
      htests α β hne hα hβ
    filter_upwards [hstage.eventually hevent] with i hi
    exact hi (w i)
  · intro α hα
    have hevent := GeometricReservations.eventually_tangent_tests enumeration henum F
      (fun n => StageWord n (n + 1))
      (fun _ w => w.latestExponent)
      (fun n w => (WordGeometry.oldDenominator F n (d n w)).map (algebraMap ℚ K))
      htests α hα
    filter_upwards [hstage.eventually hevent] with i hi
    exact hi (w i)

end UnconditionalCounterexample.ScheduledRecovery
