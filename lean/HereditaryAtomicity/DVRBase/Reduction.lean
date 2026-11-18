import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Ideal.Maps

/-!
# Algebraic reduction over a DVR

Scaling a nonzero chain over a DVR makes the initial endpoint a uniformizer power.
Every divisibility assertion in the construction is internal to the source domain.
-/

noncomputable section
namespace HereditaryAtomicity.DVRBase

variable {A R : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [CommRing R] [IsDomain R] [Algebra A R] [Algebra.IsAlgebraic A R]

/-- Every nonzero ideal in an algebraic domain over a DVR contains a power
of a specified uniformizer. The exponent may be zero. -/
theorem exists_uniformizer_pow_mem_ideal {π : A} (hπ : Irreducible π)
    (I : Ideal R) (hI : I ≠ ⊥) :
    ∃ m : ℕ, algebraMap A R π ^ m ∈ I := by
  obtain ⟨a, haI, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
  obtain ⟨b, hb0, hab⟩ :=
    (Algebra.IsAlgebraic.isAlgebraic (R := A) a).exists_nonzero_dvd
      (mem_nonZeroDivisors_of_ne_zero ha0)
  obtain ⟨m, hm⟩ := IsDiscreteValuationRing.associated_pow_irreducible hb0 hπ
  refine ⟨m, ?_⟩
  have hbI : algebraMap A R b ∈ I := I.mem_of_dvd hab haI
  have hd := (hm.map (algebraMap A R)).dvd
  rw [map_pow] at hd
  exact I.mem_of_dvd hd hbI

/-- Every nonzero element of an algebraic domain over a DVR divides a
uniformizer power in that domain. -/
theorem exists_dvd_uniformizer_pow {π : A} (hπ : Irreducible π)
    {a : R} (ha : a ≠ 0) : ∃ m : ℕ, a ∣ algebraMap A R π ^ m := by
  have hI : Ideal.span {a} ≠ (⊥ : Ideal R) := by
    intro h
    have hm : a ∈ (⊥ : Ideal R) := h ▸ Ideal.subset_span (Set.mem_singleton a)
    exact ha hm
  obtain ⟨m, hm⟩ := exists_uniformizer_pow_mem_ideal hπ (Ideal.span {a}) hI
  exact ⟨m, Ideal.mem_span_singleton.mp hm⟩

/-- In a nonfield local algebraic domain over a DVR, its uniformizer lies
in the source maximal ideal; locality of the coefficient map is a consequence. -/
theorem uniformizer_mem_maximalIdeal [IsLocalRing R]
    {π : A} (hπ : Irreducible π) (hfield : ¬ IsField R) :
    algebraMap A R π ∈ IsLocalRing.maximalIdeal R := by
  have hM : IsLocalRing.maximalIdeal R ≠ ⊥ :=
    fun h => hfield (IsLocalRing.isField_iff_maximalIdeal_eq.mpr h)
  obtain ⟨m, hm⟩ := exists_uniformizer_pow_mem_ideal hπ
    (IsLocalRing.maximalIdeal R) hM
  exact (inferInstance : (IsLocalRing.maximalIdeal R).IsPrime).mem_of_pow_mem m hm

end HereditaryAtomicity.DVRBase
