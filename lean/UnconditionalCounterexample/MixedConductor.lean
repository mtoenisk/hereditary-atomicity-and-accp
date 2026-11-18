import UnconditionalCounterexample.MixedConstruction
import UnconditionalCounterexample.MixedGlobalPlans
import UnconditionalCounterexample.SparseLocalConductor

/-!
# Conductor integration for the actual mixed construction

`WordEstimates` records the four remaining arithmetic consequences of the
actual mixed sequence: derivative escape at every actual argument, and the
correct single/pair transfer at each prime. It is an intermediate obligation,
not a family-existence assumption. Given its producer, the same extracted
listed sequence yields all local conductors and the universal same-integer
conductor in every original subring.
-/

noncomputable section
namespace UnconditionalCounterexample.MixedConductor

open Polynomial Filter GuardSupport ConstructionWords MixedConstruction
open SparseDomainValues SparseIntegerConductor LocalAlgebra

variable (S : Set PrimeIndex) (hS : S.Infinite)

abbrev poleAlgebra := PoleAlgebra.generated (poles S hS)
abbrev inclusion := SparseDomainValues.inclusion (poles S hS) (places S hS)
abbrev coordinate := SparseDomainValues.coordinate (poles S hS) (places S hS)

theorem poles_nonzero : ∀ f ∈ poles S hS, f ≠ 0 := by
  rintro f ⟨i, rfl⟩
  exact ((construction S hS).chain.raw_monic i).ne_zero

noncomputable def wordDen (n : ℕ) (w : Word n) : ℚ[X] :=
  (MixedGlobalPlans.globalPlan (construction S hS) n).wordDen w

noncomputable def wordValue (p : PrimeIndex) (n : ℕ) (w : Word n) : RatFunc ℚ_[p.val] :=
  ((raw S hS n).map (algebraMap ℚ ℚ_[p.val]) : RatFunc ℚ_[p.val]) ^ w.latestExponent /
    ((wordDen S hS n w).map (algebraMap ℚ ℚ_[p.val]) : RatFunc ℚ_[p.val])

noncomputable def wordDerivative (p : PrimeIndex) (n : ℕ) (w : Word n) (a : ℚ_[p.val]) : ℚ_[p.val] :=
  LocalInterpolation.wordDerivative ((raw S hS n).map (algebraMap ℚ ℚ_[p.val]))
    ((wordDen S hS n w).map (algebraMap ℚ ℚ_[p.val])) w.latestExponent a

/-- Explicit arithmetic intermediate obligation for the actual common sequence. -/
structure WordEstimates : Prop where
  primary_derivative : ∀ j : ℕ, ∀ᶠ n in atTop, ∀ w : Word n,
    (wordDerivative S hS ((places S hS).primes j) n w ((places S hS).primary j).val).valuation < -(n+1 : ℕ)
  guard_derivative : ∀ p : PrimeIndex, ∀ᶠ n in atTop, ∀ w : Word n,
    (wordDerivative S hS p n w ((places S hS).guard p).val).valuation < -(n+1 : ℕ)
  pair_transfer : ∀ (j s : ℕ), ∀ᶠ n in atTop, ∀ w : Word n,
    ∃ u v : padicScaledPolynomialRing ((places S hS).primes j).val s,
      (RatFunc.C (((places S hS).primes j).val : ℚ_[((places S hS).primes j).val]) ^ (2*s) *
        ((RatFunc.X - RatFunc.C ((places S hS).primary j).val) *
          (RatFunc.X - RatFunc.C ((places S hS).guard ((places S hS).primes j)).val))) ^ w.latestExponent =
      RatFunc.C (((places S hS).primes j).val : ℚ_[((places S hS).primes j).val]) ^ (n+1) *
        ((u : RatFunc ℚ_[((places S hS).primes j).val]) +
          (v : RatFunc ℚ_[((places S hS).primes j).val]) * wordValue S hS ((places S hS).primes j) n w)
  single_transfer : ∀ (p : PrimeIndex), p ∉ S → ∀ s : ℕ, ∀ᶠ n in atTop, ∀ w : Word n,
    ∃ u v : padicScaledPolynomialRing p.val s,
      (RatFunc.C (p.val : ℚ_[p.val]) ^ (2*s) * (RatFunc.X - RatFunc.C ((places S hS).guard p).val)) ^ w.latestExponent =
      RatFunc.C (p.val : ℚ_[p.val]) ^ (n+1) *
        ((u : RatFunc ℚ_[p.val]) + (v : RatFunc ℚ_[p.val]) * wordValue S hS p n w)

theorem wordDen_ne_zero (n : ℕ) (w : Word n) : wordDen S hS n w ≠ 0 := by
  unfold wordDen ConstructionWords.DegreePlan.wordDen
  apply Finset.prod_ne_zero_iff.mpr
  intro j _
  exact pow_ne_zero _ ((construction S hS).chain.raw_monic j.val).ne_zero

theorem argument_difference_unit (j : ℕ) :
    IsUnit ((places S hS).guard ((places S hS).primes j) - (places S hS).primary j) := by
  apply PairedResidues.difference_isUnit
  · apply SparsePrimaryDomain.primary_not_unit (places S hS) _ j
    exact SparsePrimaryDomain.ofSelected_primary_zero S hS _ _
  · exact (construction S hS).chain.guardChain.value_unit _

theorem conductors_of_listed_sequence (hlocal : WordEstimates S hS)
    (T : Subring (domain S hS)) (y : ℕ → T.map (inclusion S hS))
    (stage : ℕ → ℕ) (hstage : Tendsto stage atTop atTop) (w : ∀ i, Word (stage i))
    (R : ℕ) (hbound : ∀ i, (w i).latestExponent ≤ R)
    (hword : ∀ i, ((y i : poleAlgebra S hS) : RatFunc ℚ) =
      ScheduledRecovery.generators (raw S hS) (exponent S hS) (stage i) ^ (w i).latestExponent *
        (∏ j ∈ Finset.range (stage i),
          ScheduledRecovery.generators (raw S hS) (exponent S hS) j ^ (w i).oldExponent j)) :
    PairConductors (poles S hS) (poles_nonzero S hS) (places S hS) T ∧
      SingleConductors (poles S hS) (poles_nonzero S hS) (places S hS) T := by
  have hfrac (i : ℕ) : ((y i : poleAlgebra S hS) : RatFunc ℚ) =
      algebraMap ℚ[X] (RatFunc ℚ) (raw S hS (stage i)) ^ (w i).latestExponent /
        algebraMap ℚ[X] (RatFunc ℚ) (wordDen S hS (stage i) (w i)) := by
    rw [hword]
    have h := ConstructionRecovery.global_word_eq_fraction (raw S hS) (exponent S hS)
      (stage i) (MixedGlobalPlans.globalPlan (construction S hS) (stage i))
      (MixedGlobalPlans.globalPlan_E (construction S hS) (stage i)) (w i)
    rwa [ConstructionRecovery.oldDenominator_eq_wordDen] at h
  have hclock : Tendsto (fun i => stage i + 1) atTop atTop :=
    tendsto_atTop_mono (fun i => Nat.le_succ (stage i)) hstage
  have hhull := MixedGlobalPlans.hull_eq_top_of_sequence (construction S hS)
    (T.map (inclusion S hS)) y stage hstage w hword
  constructor
  · intro j
    apply SparseLocalConductor.pair_of_extracted_words (poles S hS) (poles_nonzero S hS) (places S hS)
      T hhull j (argument_difference_unit S hS j) y (fun i => raw S hS (stage i))
      (fun i => wordDen S hS (stage i) (w i)) (fun i => (w i).latestExponent)
      (fun i => stage i + 1) R (fun i => wordDen_ne_zero S hS (stage i) (w i))
      hfrac hclock (Eventually.of_forall hbound)
    · filter_upwards [hstage.eventually (hlocal.primary_derivative j)] with i hi
      exact hi (w i)
    · filter_upwards [hstage.eventually (hlocal.guard_derivative ((places S hS).primes j))] with i hi
      exact hi (w i)
    · intro s
      filter_upwards [hstage.eventually (hlocal.pair_transfer j s)] with i hi
      exact hi (w i)
  · intro p hp
    have hpS : p ∉ S := by rwa [← MixedConstruction.selected_range S hS]
    apply SparseLocalConductor.single_of_extracted_words (poles S hS) (poles_nonzero S hS) (places S hS)
      T hhull p y (fun i => raw S hS (stage i))
      (fun i => wordDen S hS (stage i) (w i)) (fun i => (w i).latestExponent)
      (fun i => stage i + 1) R (fun i => wordDen_ne_zero S hS (stage i) (w i))
      hfrac hclock (Eventually.of_forall hbound)
    · filter_upwards [hstage.eventually (hlocal.guard_derivative p)] with i hi
      exact hi (w i)
    · intro s
      filter_upwards [hstage.eventually (hlocal.single_transfer p hpS s)] with i hi
      exact hi (w i)

theorem integer_conductor_of_listed_sequence (hlocal : WordEstimates S hS)
    (T : Subring (domain S hS)) (y : ℕ → T.map (inclusion S hS))
    (stage : ℕ → ℕ) (hstage : Tendsto stage atTop atTop) (w : ∀ i, Word (stage i))
    (R : ℕ) (hbound : ∀ i, (w i).latestExponent ≤ R)
    (hword : ∀ i, ((y i : poleAlgebra S hS) : RatFunc ℚ) =
      ScheduledRecovery.generators (raw S hS) (exponent S hS) (stage i) ^ (w i).latestExponent *
        (∏ j ∈ Finset.range (stage i),
          ScheduledRecovery.generators (raw S hS) (exponent S hS) j ^ (w i).oldExponent j)) :
    (∃ n : ℕ, 0 < n ∧ (n : domain S hS) * coordinate S hS ∈ T) ∧
      ∀ n : ℕ, 0 < n → (n : domain S hS) * coordinate S hS ∈ T →
        ∀ x : domain S hS, (n : domain S hS) * x ∈ T := by
  have hhull := MixedGlobalPlans.hull_eq_top_of_sequence (construction S hS)
    (T.map (inclusion S hS)) y stage hstage w hword
  obtain ⟨hpair, hsingle⟩ := conductors_of_listed_sequence S hS hlocal T y stage hstage w R hbound hword
  exact SparseIntegerConductor.integer_conductor (poles S hS) (poles_nonzero S hS) (places S hS)
    T hhull (argument_difference_unit S hS) hpair hsingle

end UnconditionalCounterexample.MixedConductor
