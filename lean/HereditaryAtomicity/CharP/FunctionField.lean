import Mathlib.FieldTheory.SeparablyGenerated
import Mathlib.NumberTheory.ClassNumber.FunctionField

/-!
# Finite function-field foundations

An auxiliary separating coordinate gives a finite affine normalization.
Principalization of ideal classes occurs in the affine ring of integers, with omitted
poles allowed.
-/

open scoped IntermediateField Polynomial nonZeroDivisors
namespace HereditaryAtomicity.CharP.FunctionField

/-- Every transcendental element of a transcendence-degree-one field is a
transcendence basis; no finite-generation assumption on the field is needed. -/
theorem isAlgebraic_adjoin_of_trdeg_one
    (k L : Type*) [Field k] [Field L] [Algebra k L]
    (htr : Algebra.trdeg k L = 1) (t : L) (ht : Transcendental k t) :
    Algebra.IsAlgebraic k⟮t⟯ L := by
  have hind : AlgebraicIndependent k ((↑) : ({t} : Set L) → L) :=
    (algebraicIndependent_singleton_iff ⟨t, rfl⟩).mpr ht
  have hb := hind.isTranscendenceBasis_of_trdeg_le_of_finite (by simp [htr])
  convert! hb.isAlgebraic_field <;> simp


/-- A finite-type function field over a perfect field has a separating coordinate,
chosen without reference to the eventual supported base element. -/
theorem exists_separating_coordinate
    (k L : Type*) [Field k] [Field L] [Algebra k L]
    [PerfectField k] [Algebra.EssFiniteType k L]
    (htr : Algebra.trdeg k L = 1) :
    ∃ t : L, Transcendental k t ∧
      FiniteDimensional k⟮t⟯ L ∧ Algebra.IsSeparable k⟮t⟯ L := by
  classical
  obtain ⟨s, hs, hsep⟩ :=
    exists_isTranscendenceBasis_and_isSeparable_of_perfectField k L
  have hcard : s.card = 1 := by
    have h := hs.cardinalMk_eq_trdeg
    rw [htr] at h
    simpa using h
  obtain ⟨t, rfl⟩ := Finset.card_eq_one.mp hcard
  have ht : Transcendental k t :=
    hs.1.transcendental ⟨t, Finset.mem_singleton_self t⟩
  have halg : Algebra.IsAlgebraic k⟮t⟯ L := by
    convert! hs.isAlgebraic_field <;> simp
  let := halg
  let := Algebra.EssFiniteType.of_comp k k⟮t⟯ L
  exact ⟨t, ht, Algebra.finite_of_essFiniteType_of_isAlgebraic, by
    convert! hsep <;> simp⟩

/-- A finite extension of a rational-function field is finitely generated as a field. -/
theorem essFiniteType_of_finite_ratFunc
    (k L : Type*) [Field k] [Field L] [Algebra k L]
    [Algebra (RatFunc k) L] [IsScalarTower k (RatFunc k) L]
    [FunctionField k L] : Algebra.EssFiniteType k L := by
  let : Algebra.EssFiniteType k[X] (RatFunc k) :=
    Algebra.EssFiniteType.of_isLocalization (RatFunc k) k[X]⁰
  let : Algebra.EssFiniteType k (RatFunc k) :=
    Algebra.EssFiniteType.comp k k[X] (RatFunc k)
  exact Algebra.EssFiniteType.comp k (RatFunc k) L

/-- A finite rational-function extension has transcendence degree one over its constants. -/
theorem trdeg_eq_one_of_finite_ratFunc
    (k L : Type*) [Field k] [Field L] [Algebra k L]
    [Algebra k[X] L] [Algebra (RatFunc k) L]
    [IsScalarTower k k[X] L] [IsScalarTower k[X] (RatFunc k) L]
    [FunctionField k L] : Algebra.trdeg k L = 1 := by
  let : Algebra.IsAlgebraic k[X] L :=
    IsFractionRing.comap_isAlgebraic_iff.mpr (inferInstance : Algebra.IsAlgebraic (RatFunc k) L)
  let : FaithfulSMul k[X] L :=
    (faithfulSMul_iff_algebraMap_injective k[X] L).mpr
      (_root_.FunctionField.algebraMap_injective k L)
  have hb := (IsTranscendenceBasis.polynomial Unit k).algebraMap_comp (A := L)
  have heq := hb.lift_cardinalMk_eq_trdeg
  simpa using heq.symm


/-- The affine class number principalizes every integral ideal of the affine normalization. -/
theorem ideal_pow_classNumber_isPrincipal
    (k L : Type*) [Field k] [Fintype k] [Field L]
    [Algebra k[X] L] [Algebra (RatFunc k) L]
    [IsScalarTower k[X] (RatFunc k) L]
    [FunctionField k L] [Algebra.IsSeparable (RatFunc k) L]
    (I : Ideal (FunctionField.ringOfIntegers k L)) :
    (I ^ FunctionField.classNumber k L).IsPrincipal := by
  by_cases hI : I = 0
  · simp [hI, FunctionField.classNumber, Fintype.card_ne_zero, bot_isPrincipal]
  rw [← ClassGroup.mk0_eq_one_iff
      (pow_mem (mem_nonZeroDivisors_of_ne_zero hI) (FunctionField.classNumber k L))]
  convert pow_card_eq_one (x := ClassGroup.mk0 ⟨I, mem_nonZeroDivisors_of_ne_zero hI⟩) using 1
  rw [← map_pow]
  rfl


/-- A nonzero affine ideal has an actual nonzero generator after raising to the class number. -/
theorem exists_nonzero_generator_pow_classNumber
    (k L : Type*) [Field k] [Fintype k] [Field L]
    [Algebra k[X] L] [Algebra (RatFunc k) L]
    [IsScalarTower k[X] (RatFunc k) L]
    [FunctionField k L] [Algebra.IsSeparable (RatFunc k) L]
    (I : Ideal (FunctionField.ringOfIntegers k L)) (hI : I ≠ 0) :
    ∃ a : FunctionField.ringOfIntegers k L, a ≠ 0 ∧
      I ^ FunctionField.classNumber k L = Ideal.span {a} := by
  let := ideal_pow_classNumber_isPrincipal k L I
  obtain ⟨a, ha⟩ := Submodule.IsPrincipal.principal (I ^ FunctionField.classNumber k L)
  refine ⟨a, ?_, ha⟩
  intro hz
  have hpow := pow_ne_zero (FunctionField.classNumber k L) hI
  apply hpow
  simpa [hz] using ha


/-- The actual integral closure of the polynomial base is module finite
for a finite separable function-field extension. -/
theorem finite_ringOfIntegers
    (k L : Type*) [Field k] [Field L]
    [Algebra k[X] L] [Algebra (RatFunc k) L]
    [IsScalarTower k[X] (RatFunc k) L]
    [FunctionField k L] [Algebra.IsSeparable (RatFunc k) L] :
    Module.Finite k[X] (FunctionField.ringOfIntegers k L) :=
  inferInstance
end HereditaryAtomicity.CharP.FunctionField
