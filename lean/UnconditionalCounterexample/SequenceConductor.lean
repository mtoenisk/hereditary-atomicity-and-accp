import UnconditionalCounterexample.PoleTensorConductor
import UnconditionalCounterexample.SequenceLocalTransfer
import UnconditionalCounterexample.ConstructionRecovery
import UnconditionalCounterexample.SequenceDomainValues

/-!
# The paired conductor for the actual recursive sequence

The same selected sequence supplies ordinary integral domain values, the
permanent paired arguments, rational hull recovery and all local word
estimates. Along an actual extracted listed sequence with one fixed latest-
power bound, these facts give the exact conductor of the algebraic integral
tensor image. The arithmetic precision is the raw stage plus one throughout.

The only subring-specific input is the actual escaping listed sequence;
its extraction from unbounded nonunit decomposition lengths is a separate
proved interface. No local estimate, ideal power or conductor conclusion is
assumed by the endpoint.
-/

noncomputable section
namespace UnconditionalCounterexample.SequenceConductor

open Polynomial Filter StageRecursion ConstructionWords PrimaryChoices
open SequenceDomainValues

variable {R : Requirements} (seq : Sequence R)

theorem raw_nonzero : ∀ f ∈ Set.range seq.chain.raw, f ≠ 0 := by
  rintro f ⟨n, rfl⟩
  exact (seq.chain.raw_monic n).ne_zero

/-- All original domain values and all local stage estimates are supplied by
the same actual recursive sequence. Only the actual extracted listed sequence
and its fixed latest-power bound remain as subring-specific inputs. -/
theorem conductor_eq_pair_of_listed_sequence
    (T : Subring (PoleAlgebra.generated (Set.range seq.chain.raw)))
    (hTD : T ≤ domainInPole seq)
    (y : ℕ → T) (stage : ℕ → ℕ) (hstage : Tendsto stage atTop atTop)
    (w : ∀ i, Word (stage i)) (bound : ℕ)
    (hbound : ∀ i, (w i).latestExponent ≤ bound)
    (hword : ∀ i, ((y i : PoleAlgebra.generated (Set.range seq.chain.raw)) : RatFunc ℚ) =
      ScheduledRecovery.generators seq.chain.raw seq.chain.exponent (stage i) ^ (w i).latestExponent *
        (∏ j ∈ Finset.range (stage i),
          ScheduledRecovery.generators seq.chain.raw seq.chain.exponent j ^ (w i).oldExponent j))
    (j : ℕ) :
    RadicalConductor.conductorIdeal
      (PoleTensorConductor.image (primes j).val (Set.range seq.chain.raw) (raw_nonzero seq) T) =
      Ideal.span {algebraMap ℚ_[(primes j).val][X]
        (PoleAlgebra.generated (ScalarExtension.extendedSet ℚ ℚ_[(primes j).val]
          (Set.range seq.chain.raw)))
        ((X - C (SequenceLocalTransfer.branch seq j false)) *
          (X - C (SequenceLocalTransfer.branch seq j true)))} := by
  have hfrac (i : ℕ) : ((y i : PoleAlgebra.generated (Set.range seq.chain.raw)) : RatFunc ℚ) =
      algebraMap ℚ[X] (RatFunc ℚ) (seq.chain.raw (stage i)) ^ (w i).latestExponent /
        algebraMap ℚ[X] (RatFunc ℚ) ((GlobalPlans.globalPlan seq (stage i)).wordDen (w i)) := by
    rw [hword]
    have h := ConstructionRecovery.global_word_eq_fraction seq.chain.raw seq.chain.exponent
      (stage i) (GlobalPlans.globalPlan seq (stage i)) (GlobalPlans.globalPlan_E seq (stage i)) (w i)
    rwa [ConstructionRecovery.oldDenominator_eq_wordDen] at h
  have hclock : Tendsto (fun i => stage i + 1) atTop atTop :=
    tendsto_atTop_mono (fun i => Nat.le_succ (stage i)) hstage
  have hretained (b : Bool) : ∀ f ∈ Set.range seq.chain.raw,
      f.eval₂ (algebraMap ℚ ℚ_[(primes j).val]) (SequenceLocalTransfer.branch seq j b) ≠ 0 := by
    rintro f ⟨n, rfl⟩
    exact SequenceLocalTransfer.raw_eval_ne_zero seq n j b
  apply PoleTensorConductor.conductor_eq_pair_of_extracted_words
    (primes j).val (Set.range seq.chain.raw) (raw_nonzero seq) T (domainInPole seq) hTD
    (ConstructionRecovery.hull_eq_top_of_sequence seq T y stage hstage w hword)
    (SequenceLocalTransfer.branch seq j false) (SequenceLocalTransfer.branch seq j true)
    (SequenceLocalTransfer.branch_ne seq j)
    (SequenceLocalTransfer.branch_integral seq j false)
    (SequenceLocalTransfer.branch_integral seq j true)
    (hretained false) (hretained true) (norm_eval_le_one_inPole seq j false) (norm_eval_le_one_inPole seq j true)
    y (fun i => seq.chain.raw (stage i))
    (fun i => (GlobalPlans.globalPlan seq (stage i)).wordDen (w i))
    (fun i => (w i).latestExponent) (fun i => stage i + 1) bound
    (fun i => SequenceLocalTransfer.global_wordDen_eval_ne_zero seq (stage i) (w i) j false)
    (fun i => SequenceLocalTransfer.global_wordDen_eval_ne_zero seq (stage i) (w i) j true)
    hfrac hclock (Eventually.of_forall hbound)
  · filter_upwards [hstage.eventually (SequenceLocalTransfer.eventually_all_word_estimates seq j 0)]
      with i hi
    exact (hi (w i)).1 false
  · filter_upwards [hstage.eventually (SequenceLocalTransfer.eventually_all_word_estimates seq j 0)]
      with i hi
    exact (hi (w i)).1 true
  · intro s
    filter_upwards [hstage.eventually (SequenceLocalTransfer.eventually_all_word_estimates seq j s)]
      with i hi
    exact (hi (w i)).2

end UnconditionalCounterexample.SequenceConductor