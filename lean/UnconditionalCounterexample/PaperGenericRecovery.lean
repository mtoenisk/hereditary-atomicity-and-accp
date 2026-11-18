import UnconditionalCounterexample.PaperExtractionValues
import UnconditionalCounterexample.PaperInclusion
import UnconditionalCounterexample.UnboundedWords

/-!
# Generic recovery for subrings of the single constructed domain

An intrinsically unbounded nonzero element of an arbitrary original subring
supplies actual listed words with one uniform exponent budget. All profile,
unit, factorization and geometric inputs are supplied by PaperConstruction.
The same sequence recovers the full rational pole algebra and clears each
original-domain element, including the coordinate, by a positive integer.
-/

namespace UnconditionalCounterexample.PaperGenericRecovery

open Polynomial Filter RawWords
open PaperConstruction PaperInclusion

noncomputable local instance : Algebra ℚ (RatFunc ℚ) := RatFunc.instAlgebraOfPolynomial ℚ ℚ

/-- Actual uniformly bounded listed words in the image of the original subring,
extracted from intrinsic unbounded factorizations in that subring. -/
theorem exists_listed_sequence_of_unbounded
    (T : Subring domain) (x : T) (hx : x ≠ 0)
    (hunbounded : ¬ Factorization.HasBoundedFactorizations x) :
    ∃ r : ℕ, 0 < r ∧ ∃ y : ℕ → T.map inclusion, ∃ stage : ℕ → ℕ,
      ∃ w : ∀ i, StageWord (stage i) (stage i + 1),
      (∀ i, i < stage i) ∧ Tendsto stage atTop atTop ∧
      (∀ i, (w i).latestExponent ≤ 2 * r) ∧
      (∀ i j, |(w i).oldExponent j| ≤ (2 * r : ℕ)) ∧ ∀ i,
        ((y i : poleAlgebra) : RatFunc ℚ) =
          ScheduledRecovery.generators raw exponent (stage i) ^ (w i).latestExponent *
          (∏ j ∈ Finset.range (stage i),
            ScheduledRecovery.generators raw exponent j ^ (w i).oldExponent j) := by
  apply UnboundedWords.exists_listed_sequence_of_unbounded_map raw
    (fun i => ⟨construction.chain.raw_monic i, construction.chain.raw_irreducible i⟩)
    (fun _ _ h => construction.chain.raw_degree_strict.injective (congrArg natDegree h))
    exponent (fun j => PairedDomain.vertical places (.inl j))
    (GuardSupport.guardEvaluation places.guard places.guard_trans)
    generator_b_valuation generator_q_valuation (fun p i => generator_guard_valuation i p)
    inclusion inclusion_injective valuationProfiles
    primary_value_eq_exp_profile guard_value_eq_one_of_outside_zero inverse_pole_mem_of_pure
    T (subring_reflects_units T) x hx hunbounded

/-- The same actual sequence and its geometric tests recover the full rational
pole algebra from an unbounded nonzero element of an arbitrary original T. -/
theorem hull_eq_top_of_unbounded
    (T : Subring domain) (x : T) (hx : x ≠ 0)
    (hunbounded : ¬ Factorization.HasBoundedFactorizations x) :
    RationalHull.hull (T.map inclusion) = ⊤ := by
  obtain ⟨r, hr, y, stage, w, hlarge, hstage, hbound, hold, hword⟩ :=
    exists_listed_sequence_of_unbounded T x hx hunbounded
  exact ConstructionRecovery.hull_eq_top_of_sequence construction
    (T.map inclusion) y stage hstage w hword

/-- Every original-domain element has a positive integer multiple in T.
The integer is allowed to depend on the element. -/
theorem exists_nat_mul_mem_of_unbounded
    (T : Subring domain) (x : T) (hx : x ≠ 0)
    (hunbounded : ¬ Factorization.HasBoundedFactorizations x) (z : domain) :
    ∃ n : ℕ, 0 < n ∧ (n : domain) * z ∈ T :=
  PaperInclusion.exists_nat_mul_mem T (hull_eq_top_of_unbounded T x hx hunbounded) z

/-- A positive integer multiple of the literal rational coordinate belongs to T. -/
theorem exists_nat_coordinate_mem_of_unbounded
    (T : Subring domain) (x : T) (hx : x ≠ 0)
    (hunbounded : ¬ Factorization.HasBoundedFactorizations x) :
    ∃ n : ℕ, 0 < n ∧ (n : domain) * coordinate ∈ T :=
  exists_nat_mul_mem_of_unbounded T x hx hunbounded coordinate

end UnconditionalCounterexample.PaperGenericRecovery
