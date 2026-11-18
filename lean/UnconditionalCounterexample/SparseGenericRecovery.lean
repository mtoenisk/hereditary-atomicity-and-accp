import UnconditionalCounterexample.MixedConstruction
import UnconditionalCounterexample.MixedGlobalPlans
import UnconditionalCounterexample.SparseDomainValues
import UnconditionalCounterexample.SparseExtraction
import UnconditionalCounterexample.MixedGeneratorProfiles

/-!
# Generic recovery for the constructed sparse-primary domains

For every infinite set of selected primes, the actual mixed polynomial sequence
supplies the geometric recovery theorem. Intrinsic unbounded factorizations in
an original subring yield a listed sequence with one uniform exponent budget;
that same sequence recovers the full rational pole algebra. Positive integer
clearing then returns to the original subring through the canonical inclusion.
-/

noncomputable section
namespace UnconditionalCounterexample.SparseGenericRecovery
open Polynomial Filter RawWords GuardSupport MixedConstruction

noncomputable local instance : Algebra ℚ (RatFunc ℚ) := RatFunc.instAlgebraOfPolynomial ℚ ℚ

variable (S : Set PrimeIndex) (hS : S.Infinite)

abbrev poleAlgebra := PoleAlgebra.generated (poles S hS)

/-- The actual sparse domain's canonical inclusion in its own pole algebra. -/
abbrev inclusion : domain S hS →+* poleAlgebra S hS :=
  SparseDomainValues.inclusion (poles S hS) (places S hS)

abbrev coordinate : domain S hS :=
  SparseDomainValues.coordinate (poles S hS) (places S hS)

/-- Extraction in the actual mixed domain from intrinsic unbounded factorization;
all normalized column and realization inputs come from the constructed sequence. -/
theorem exists_listed_sequence_of_unbounded
    (T : Subring (domain S hS)) (x : T) (hx : x ≠ 0)
    (hunbounded : ¬ Factorization.HasBoundedFactorizations x) :
    ∃ r : ℕ, 0 < r ∧ ∃ y : ℕ → T.map (inclusion S hS), ∃ stage : ℕ → ℕ,
      ∃ w : ∀ i, StageWord (stage i) (stage i + 1),
      (∀ i, i < stage i) ∧ Tendsto stage atTop atTop ∧
      (∀ i, (w i).latestExponent ≤ 2 * r) ∧
      (∀ i j, |(w i).oldExponent j| ≤ (2 * r : ℕ)) ∧ ∀ i,
        ((y i : poleAlgebra S hS) : RatFunc ℚ) =
          ScheduledRecovery.generators (raw S hS) (exponent S hS) (stage i) ^ (w i).latestExponent *
          (∏ j ∈ Finset.range (stage i),
            ScheduledRecovery.generators (raw S hS) (exponent S hS) j ^ (w i).oldExponent j) := by
  exact SparseExtraction.exists_listed_sequence_of_unbounded (raw S hS)
    (fun i => ⟨(construction S hS).chain.raw_monic i,
      (construction S hS).chain.raw_irreducible i⟩)
    (fun _ _ h => (construction S hS).chain.raw_degree_strict.injective (congrArg natDegree h))
    (construction S hS).chain.raw_constant_ne_zero (exponent S hS) (places S hS)
    (MixedGeneratorProfiles.generatorProfiles S hS) (guardSupport S hS) T x hx hunbounded

/-- The actual selected mixed plans recover the pole algebra from the same
listed sequence in the image of an original sparse-domain subring. -/
theorem hull_eq_top_of_listed_sequence
    (T : Subring (domain S hS)) (y : ℕ → T.map (inclusion S hS))
    (stage : ℕ → ℕ) (hstage : Tendsto stage atTop atTop)
    (w : ∀ i, StageWord (stage i) (stage i + 1))
    (hword : ∀ i, ((y i : poleAlgebra S hS) : RatFunc ℚ) =
      ScheduledRecovery.generators (raw S hS) (exponent S hS) (stage i) ^ (w i).latestExponent *
      (∏ j ∈ Finset.range (stage i),
        ScheduledRecovery.generators (raw S hS) (exponent S hS) j ^ (w i).oldExponent j)) :
    RationalHull.hull (T.map (inclusion S hS)) = ⊤ :=
  MixedGlobalPlans.hull_eq_top_of_sequence (construction S hS)
    (T.map (inclusion S hS)) y stage hstage w hword

/-- Integer clearing returns through the literal injective inclusion to the
original subring; the integer may depend on the chosen domain element. -/
theorem exists_nat_mul_mem_of_listed_sequence
    (T : Subring (domain S hS)) (y : ℕ → T.map (inclusion S hS))
    (stage : ℕ → ℕ) (hstage : Tendsto stage atTop atTop)
    (w : ∀ i, StageWord (stage i) (stage i + 1))
    (hword : ∀ i, ((y i : poleAlgebra S hS) : RatFunc ℚ) =
      ScheduledRecovery.generators (raw S hS) (exponent S hS) (stage i) ^ (w i).latestExponent *
      (∏ j ∈ Finset.range (stage i),
        ScheduledRecovery.generators (raw S hS) (exponent S hS) j ^ (w i).oldExponent j))
    (z : domain S hS) : ∃ n : ℕ, 0 < n ∧ (n : domain S hS) * z ∈ T :=
  SparseDomainValues.exists_nat_mul_mem (poles S hS) (places S hS) T
    (hull_eq_top_of_listed_sequence S hS T y stage hstage w hword) z

theorem hull_eq_top_of_unbounded
    (T : Subring (domain S hS)) (x : T) (hx : x ≠ 0)
    (hunbounded : ¬ Factorization.HasBoundedFactorizations x) :
    RationalHull.hull (T.map (inclusion S hS)) = ⊤ := by
  obtain ⟨r, hr, y, stage, w, hlarge, hstage, hbound, hold, hword⟩ :=
    exists_listed_sequence_of_unbounded S hS T x hx hunbounded
  exact hull_eq_top_of_listed_sequence S hS T y stage hstage w hword

theorem exists_nat_mul_mem_of_unbounded
    (T : Subring (domain S hS)) (x : T) (hx : x ≠ 0)
    (hunbounded : ¬ Factorization.HasBoundedFactorizations x) (z : domain S hS) :
    ∃ n : ℕ, 0 < n ∧ (n : domain S hS) * z ∈ T :=
  SparseDomainValues.exists_nat_mul_mem (poles S hS) (places S hS) T
    (hull_eq_top_of_unbounded S hS T x hx hunbounded) z

/-- A positive integer multiple of the literal rational coordinate belongs to T. -/
theorem exists_nat_coordinate_mem_of_unbounded
    (T : Subring (domain S hS)) (x : T) (hx : x ≠ 0)
    (hunbounded : ¬ Factorization.HasBoundedFactorizations x) :
    ∃ n : ℕ, 0 < n ∧ (n : domain S hS) * coordinate S hS ∈ T :=
  exists_nat_mul_mem_of_unbounded S hS T x hx hunbounded (coordinate S hS)

end UnconditionalCounterexample.SparseGenericRecovery
