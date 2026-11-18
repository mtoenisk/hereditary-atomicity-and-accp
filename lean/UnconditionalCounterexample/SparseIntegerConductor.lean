import UnconditionalCounterexample.SparseDomainValues
import UnconditionalCounterexample.TensorPairLifting
import UnconditionalCounterexample.SingleTensorLifting
import UnconditionalCounterexample.PairedResidues

/-!
# The same integer conductor with one or two arguments at each prime

The original sparse-primary intersection retains a guard at every rational
prime. At a selected prime the two integral value vectors lift the prescribed
integer n; outside the selected set, integral constants lift the sole value
and no multiplier is needed. Finite-cyclic tensor descent then gives nD in the
original T, for the very same integer with nt in T.

The generic theorem keeps rational hull recovery and the actual local conductor
equalities explicit until the mixed recursive construction supplies them.
-/

noncomputable section
namespace UnconditionalCounterexample.SparseIntegerConductor

open Polynomial SparsePrimaryDomain SparseDomainValues GuardSupport
open LocalAlgebra RadicalConductor
open scoped TensorProduct

variable (S : Set ℚ[X]) (hS : ∀ f ∈ S, f ≠ 0) (d : Places)

abbrev localImage (p : PrimeIndex) (T : Subring (domain S d)) :=
  PoleTensorConductor.image p.val S hS (T.map (inclusion S d))

def PairConductors (T : Subring (domain S d)) : Prop :=
  ∀ j : ℕ, conductorIdeal (localImage S hS d (d.primes j) T) = Ideal.span
    {algebraMap ℚ_[(d.primes j).val][X]
      (PoleAlgebra.generated (ScalarExtension.extendedSet ℚ ℚ_[(d.primes j).val] S))
      ((X - C (d.primary j).val) * (X - C (d.guard (d.primes j)).val))}

def SingleConductors (T : Subring (domain S d)) : Prop :=
  ∀ p : PrimeIndex, p ∉ Set.range d.primes →
    conductorIdeal (localImage S hS d p T) = Ideal.span
      {algebraMap ℚ_[p.val][X] (PoleAlgebra.generated (ScalarExtension.extendedSet ℚ ℚ_[p.val] S))
        (X - C (d.guard p).val)}

theorem same_integer (T : Subring (domain S d))
    (hhull : RationalHull.hull (T.map (inclusion S d)) = ⊤)
    (hdiff : ∀ j, IsUnit (d.guard (d.primes j) - d.primary j))
    (hpair : PairConductors S hS d T) (hsingle : SingleConductors S hS d T)
    (n : ℕ) (hnt : (n : domain S d) * coordinate S d ∈ T) :
    ∀ x : domain S d, (n : domain S d) * x ∈ T := by
  classical
  have hntB : (n : poleAlgebra S) * algebraMap ℚ[X] (poleAlgebra S) X ∈ T.map (inclusion S d) := by
    exact ⟨_, hnt, by rw [map_mul, map_natCast, inclusion_coordinate]⟩
  have hindexed (p : PrimeIndex) :
      ∀ z ∈ IntegralTensorImage.image p.val (poleAlgebra S) (domainInPole S d),
      (n : ℚ_[p.val] ⊗[ℚ] poleAlgebra S) * z ∈
        IntegralTensorImage.image p.val (poleAlgebra S) (T.map (inclusion S d)) := by
    by_cases hp : p ∈ Set.range d.primes
    · obtain ⟨j, rfl⟩ := hp
      have ha (f : ℚ[X]) (hf : f ∈ S) :
          f.eval₂ (algebraMap ℚ ℚ_[(d.primes j).val]) (d.primary j).val ≠ 0 := by
        apply mt _ (hS f hf)
        exact (transcendental_iff.mp (d.primary_trans j)) f
      have hb (f : ℚ[X]) (hf : f ∈ S) :
          f.eval₂ (algebraMap ℚ ℚ_[(d.primes j).val]) (d.guard (d.primes j)).val ≠ 0 := by
        apply mt _ (hS f hf)
        exact (transcendental_iff.mp (d.guard_trans (d.primes j))) f
      intro z hz
      simpa only [Int.cast_natCast] using TensorPairLifting.same_integer_in_image
        (d.primes j).val S hS (T.map (inclusion S d)) (domainInPole S d)
        (d.primary j) (d.guard (d.primes j)) (hdiff j) ha hb
        (primary_norm_eval_le_one_inPole S d j) (guard_norm_eval_le_one_inPole S d (d.primes j))
        (hpair j) (n : ℤ) (by simpa only [Int.cast_natCast] using hntB) z hz
    · have hb (f : ℚ[X]) (hf : f ∈ S) :
          f.eval₂ (algebraMap ℚ ℚ_[p.val]) (d.guard p).val ≠ 0 := by
        apply mt _ (hS f hf)
        exact (transcendental_iff.mp (d.guard_trans p)) f
      intro z hz
      simpa only [Int.cast_natCast] using SingleTensorLifting.same_integer_in_image
        p.val S hS (T.map (inclusion S d)) (domainInPole S d) (d.guard p).val hb
        (guard_norm_eval_le_one_inPole S d p) (hsingle p hp) (n : ℤ) z hz
  have hall := TorsionDescent.integer_conductor_of_all_images
    (T.map (inclusion S d)) (domainInPole S d) hhull (n : ℤ)
    (fun p hp => by simpa only [Int.cast_natCast] using hindexed ⟨p, hp.out⟩)
  intro x
  obtain ⟨y, hy, hey⟩ := hall (inclusion S d x) x.property
  have he : y = (n : domain S d) * x := inclusion_injective S d (by
    simpa only [map_mul, map_natCast, Int.cast_natCast] using hey)
  exact he ▸ hy

/-- Source hypotheses on the two actual integral arguments imply the required unit difference. -/
theorem same_integer_of_primary_nonunit_guard_unit (T : Subring (domain S d))
    (hhull : RationalHull.hull (T.map (inclusion S d)) = ⊤)
    (hprimary : ∀ j, ¬ IsUnit (d.primary j)) (hguard : ∀ p, IsUnit (d.guard p))
    (hpair : PairConductors S hS d T) (hsingle : SingleConductors S hS d T)
    (n : ℕ) (hnt : (n : domain S d) * coordinate S d ∈ T) :
    ∀ x : domain S d, (n : domain S d) * x ∈ T :=
  same_integer S hS d T hhull
    (fun j => PairedResidues.difference_isUnit _ _ (hprimary j) (hguard (d.primes j)))
    hpair hsingle n hnt

/-- Existence and the universal same-integer statement for the sparse intersection. -/
theorem integer_conductor (T : Subring (domain S d))
    (hhull : RationalHull.hull (T.map (inclusion S d)) = ⊤)
    (hdiff : ∀ j, IsUnit (d.guard (d.primes j) - d.primary j))
    (hpair : PairConductors S hS d T) (hsingle : SingleConductors S hS d T) :
    (∃ n : ℕ, 0 < n ∧ (n : domain S d) * coordinate S d ∈ T) ∧
      ∀ n : ℕ, 0 < n → (n : domain S d) * coordinate S d ∈ T →
        ∀ x : domain S d, (n : domain S d) * x ∈ T :=
  ⟨exists_nat_coordinate_mem S d T hhull,
    fun n _ hnt => same_integer S hS d T hhull hdiff hpair hsingle n hnt⟩

end UnconditionalCounterexample.SparseIntegerConductor
