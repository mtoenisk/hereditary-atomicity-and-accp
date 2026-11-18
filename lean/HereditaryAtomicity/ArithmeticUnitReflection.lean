import HereditaryAtomicity.SemilocalBasics
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic

/-!
# Unit reflection and semilocality

Finite prime avoidance shows that a unit-reflecting homomorphism to a semilocal ring
makes every source maximal ideal the contraction of a target maximal ideal.
-/

noncomputable section

namespace HereditaryAtomicity

universe u v

/-- A unit-reflecting map into a semilocal nontrivial ring makes every source
maximal ideal the contraction of an actual target maximal ideal. -/
theorem maximalIdeal_eq_comap_of_unit_reflection
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Nontrivial S]
    [Finite (MaximalSpectrum S)] (f : R →+* S)
    (hunit : ∀ x : R, IsUnit (f x) → IsUnit x) (M : MaximalSpectrum R) :
    ∃ N : MaximalSpectrum S, Ideal.comap f N.asIdeal = M.asIdeal := by
  classical
  let N₀ : MaximalSpectrum S := Classical.choice inferInstance
  have hcover : (M.asIdeal : Set R) ⊆
      ⋃ N ∈ (Set.univ : Set (MaximalSpectrum S)), (Ideal.comap f N.asIdeal : Set R) := by
    intro x hx
    have hnonunit : ¬ IsUnit (f x) := fun h =>
      M.isMaximal.ne_top (M.asIdeal.eq_top_of_isUnit_mem hx (hunit x h))
    obtain ⟨N, hN, hxN⟩ := exists_max_ideal_of_mem_nonunits hnonunit
    exact Set.mem_iUnion.mpr ⟨⟨N, hN⟩, Set.mem_iUnion.mpr ⟨Set.mem_univ _, hxN⟩⟩
  obtain ⟨N, _, hMN⟩ :=
    (Ideal.subset_union_prime_finite (Set.toFinite _) N₀ N₀
      (fun N _ _ _ => N.isMaximal.isPrime.comap f)).mp hcover
  exact ⟨N, (M.isMaximal.eq_of_le (Ideal.IsPrime.ne_top (N.isMaximal.isPrime.comap f))
    hMN).symm⟩

/-- Semilocality descends through a unit-reflecting homomorphism. -/
theorem finite_maximalSpectrum_of_unit_reflection
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Nontrivial S]
    [Finite (MaximalSpectrum S)] (f : R →+* S)
    (hunit : ∀ x : R, IsUnit (f x) → IsUnit x) : Finite (MaximalSpectrum R) := by
  classical
  choose N hN using maximalIdeal_eq_comap_of_unit_reflection f hunit
  apply Finite.of_injective N
  intro M M' h
  apply MaximalSpectrum.ext
  rw [← hN M, ← hN M', h]

/-- In particular, a unit-reflecting subring of a semilocal ring is semilocal. -/
theorem finite_maximalSpectrum_subring_of_unit_reflection
    {R : Type u} [CommRing R] [Nontrivial R] [Finite (MaximalSpectrum R)]
    (A : Subring R) (hunit : ∀ a : A, IsUnit (a : R) → IsUnit a) :
    Finite (MaximalSpectrum A) :=
  finite_maximalSpectrum_of_unit_reflection A.subtype hunit

/-- Integral extensions of actual subrings reflect units. -/
theorem subring_isUnit_of_integral
    {R : Type u} [CommRing R] (A : Subring R) [Algebra.IsIntegral A R]
    (a : A) (ha : IsUnit (a : R)) : IsUnit a := by
  change IsUnit ((algebraMap A R) a) at ha
  exact ha.of_map (algebraMap A R)

end HereditaryAtomicity
