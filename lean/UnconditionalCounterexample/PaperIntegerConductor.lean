import UnconditionalCounterexample.PaperGenericRecovery
import UnconditionalCounterexample.PaperLocalConductor
import UnconditionalCounterexample.TensorPairLifting
import UnconditionalCounterexample.SequenceDomainValues
import UnconditionalCounterexample.PairedResidues

/-!
# The integer conductor of the original subring

Theorem 6.3 uses one escaping sequence in the image of the original subring
for both generic recovery and the paired conductors. The integral pair
lattice and cyclic torsion descent apply to every positive integer n for
which the original subring contains nt.
-/

noncomputable section
namespace UnconditionalCounterexample.PaperIntegerConductor

open Polynomial PrimaryChoices PaperConstruction PaperInclusion SequenceDomainValues
open LocalAlgebra RadicalConductor
open scoped TensorProduct

private theorem pole_nonzero (f : ℚ[X]) (hf : f ∈ poles) : f ≠ 0 := by
  obtain ⟨j, rfl⟩ := hf
  exact (construction.chain.raw_monic j).ne_zero

/-- Descend the paired conductors at the actual permanent arguments for the
original unital subring, with the same integer that clears the coordinate. -/
theorem same_integer (T : Subring domain) (hhull : RationalHull.hull (T.map inclusion) = ⊤)
    (hcond : ∀ j, conductorIdeal (PoleTensorConductor.image (primes j).val poles
      pole_nonzero (T.map inclusion)) = Ideal.span {algebraMap ℚ_[(primes j).val][X]
        (PoleAlgebra.generated (ScalarExtension.extendedSet ℚ ℚ_[(primes j).val] poles))
        ((X - C (SequenceLocalTransfer.branch construction j false)) *
          (X - C (SequenceLocalTransfer.branch construction j true)))})
    (n : ℕ) (hnt : (n : domain) * coordinate ∈ T) :
    ∀ x : domain, (n : domain) * x ∈ T := by
  let D := domainInPole construction
  have hntB : (n : poleAlgebra) * algebraMap ℚ[X] poleAlgebra X ∈ T.map inclusion := by
    exact ⟨_, hnt, by rw [map_mul, map_natCast, inclusion_coordinate]; rfl⟩
  have hindexed (q : GuardSupport.PrimeIndex) :
      ∀ z ∈ IntegralTensorImage.image q.val poleAlgebra D,
      (n : ℚ_[q.val] ⊗[ℚ] poleAlgebra) * z ∈ IntegralTensorImage.image q.val poleAlgebra (T.map inclusion) := by
    obtain ⟨j, rfl⟩ := primes.surjective q
    let a := PrimaryChoices.primary j
    let b := construction.chain.guardChain.value (primes j)
    have hd : IsUnit (b - a) := PairedResidues.difference_isUnit a b
      (CombinedGuardStep.primary_not_unit j) (construction.chain.guardChain.value_unit _)
    have hretained (u : Bool) (f : ℚ[X]) (hf : f ∈ poles) :
        f.eval₂ (algebraMap ℚ ℚ_[(primes j).val]) (SequenceLocalTransfer.branch construction j u) ≠ 0 := by
      apply mt _ (pole_nonzero f hf)
      exact (transcendental_iff.mp (SequenceLocalTransfer.branch_transcendental construction j u)) f
    intro z hz
    simpa only [Int.cast_natCast] using TensorPairLifting.same_integer_in_image
      (primes j).val poles pole_nonzero (T.map inclusion) D a b hd (hretained false) (hretained true)
      (norm_eval_le_one_inPole construction j false) (norm_eval_le_one_inPole construction j true)
      (hcond j) (n : ℤ) (by simpa only [Int.cast_natCast] using hntB) z hz
  have hall := TorsionDescent.integer_conductor_of_all_images (T.map inclusion) D hhull (n : ℤ)
    (fun p hp => by simpa only [Int.cast_natCast] using hindexed ⟨p, hp.out⟩)
  intro x
  obtain ⟨y, hy, hey⟩ := hall (inclusion x) x.property
  have he : y = (n : domain) * x := inclusion_injective (by
    simpa only [map_mul, map_natCast, Int.cast_natCast] using hey)
  exact he ▸ hy

/-- Manuscript Theorem 6.3 for every unital subring of the constructed domain. -/
theorem integer_conductor (T : Subring domain) (x : T) (hx : x ≠ 0)
    (hu : ¬ Factorization.HasBoundedFactorizations x) :
    (∃ n : ℕ, 0 < n ∧ (n : domain) * coordinate ∈ T) ∧
      ∀ n : ℕ, 0 < n → (n : domain) * coordinate ∈ T → ∀ z : domain, (n : domain) * z ∈ T := by
  obtain ⟨r, _, y, stage, w, _, hstage, hbound, _, hword⟩ :=
    PaperGenericRecovery.exists_listed_sequence_of_unbounded T x hx hu
  have hhull := ConstructionRecovery.hull_eq_top_of_sequence construction
    (T.map inclusion) y stage hstage w hword
  refine ⟨PaperInclusion.exists_nat_coordinate_mem T hhull, fun n _ hnt => ?_⟩
  exact same_integer T hhull
    (PaperLocalConductor.conductor_eq_pair_of_listed_sequence T y stage hstage w (2 * r) hbound hword)
    n hnt

theorem exists_integer_conductor (T : Subring domain) (hT : ¬ Factorization.IsBFDomain T) :
    ∃ m : ℕ, 0 < m ∧ ∀ z : domain, (m : domain) * z ∈ T := by
  classical
  unfold Factorization.IsBFDomain at hT
  push Not at hT
  obtain ⟨x, hx, hu⟩ := hT
  obtain ⟨⟨n, hn, hnt⟩, hall⟩ := integer_conductor T x hx hu
  exact ⟨n, hn, hall n hn hnt⟩

end UnconditionalCounterexample.PaperIntegerConductor
