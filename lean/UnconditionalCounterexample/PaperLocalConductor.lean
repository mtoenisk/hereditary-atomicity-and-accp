import UnconditionalCounterexample.PaperInclusion
import UnconditionalCounterexample.SequenceConductor

/-!
# Local conductors for subrings of the single constructed domain

Specialize the actual sequence conductor to PaperConstruction.domain and the
canonical PaperInclusion map. Every original unital subring is handled via its
actual image in the pole algebra. Original domain evaluations are exported
separately for the same-integer pair-lattice step.

The current endpoint consumes the actual extracted bounded listed sequence.
The separate PaperGenericRecovery extraction supplies that sequence from an
element with unbounded intrinsic nonunit decomposition lengths.
-/

noncomputable section
namespace UnconditionalCounterexample.PaperLocalConductor

open Polynomial Filter ConstructionWords PrimaryChoices

def localImage (j : ℕ) (T : Subring PaperConstruction.domain) :
    Subring (PoleAlgebra.generated
      (ScalarExtension.extendedSet ℚ ℚ_[(primes j).val] PaperConstruction.poles)) :=
  PoleTensorConductor.image (primes j).val PaperConstruction.poles
    (SequenceConductor.raw_nonzero PaperConstruction.construction) (T.map PaperInclusion.inclusion)

theorem original_norm_eval_le_one (j : ℕ) (b : Bool) (x : PaperConstruction.domain) :
    ‖RatFunc.eval (algebraMap ℚ ℚ_[(primes j).val])
      (SequenceLocalTransfer.branch PaperConstruction.construction j b) (x : RatFunc ℚ)‖ ≤ 1 :=
  SequenceDomainValues.norm_eval_le_one PaperConstruction.construction j b x x.property

theorem mapped_subring_le_domainInPole (T : Subring PaperConstruction.domain) :
    T.map PaperInclusion.inclusion ≤
      SequenceDomainValues.domainInPole PaperConstruction.construction := by
  intro x hx
  have h := PaperInclusion.map_subring_le_range T hx
  rw [PaperInclusion.range_eq_comap] at h
  exact h

/-- Exact local conductor for an arbitrary original subring of the single
constructed domain, using its actual extracted listed sequence. -/
theorem conductor_eq_pair_of_listed_sequence
    (T : Subring PaperConstruction.domain)
    (y : ℕ → T.map PaperInclusion.inclusion) (stage : ℕ → ℕ)
    (hstage : Tendsto stage atTop atTop) (w : ∀ i, Word (stage i)) (bound : ℕ)
    (hbound : ∀ i, (w i).latestExponent ≤ bound)
    (hword : ∀ i, ((y i : PaperInclusion.poleAlgebra) : RatFunc ℚ) =
      ScheduledRecovery.generators PaperConstruction.raw PaperConstruction.exponent (stage i) ^
        (w i).latestExponent *
        (∏ j ∈ Finset.range (stage i), ScheduledRecovery.generators
          PaperConstruction.raw PaperConstruction.exponent j ^ (w i).oldExponent j))
    (j : ℕ) :
    RadicalConductor.conductorIdeal (localImage j T) = Ideal.span
      {algebraMap ℚ_[(primes j).val][X]
        (PoleAlgebra.generated (ScalarExtension.extendedSet ℚ ℚ_[(primes j).val] PaperConstruction.poles))
        ((X - C (SequenceLocalTransfer.branch PaperConstruction.construction j false)) *
          (X - C (SequenceLocalTransfer.branch PaperConstruction.construction j true)))} :=
  SequenceConductor.conductor_eq_pair_of_listed_sequence PaperConstruction.construction
    (T.map PaperInclusion.inclusion) (mapped_subring_le_domainInPole T)
    y stage hstage w bound hbound hword j

end UnconditionalCounterexample.PaperLocalConductor