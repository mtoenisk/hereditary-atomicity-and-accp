import HereditaryAtomicity.DVRBase.CoefficientDivision
import HereditaryAtomicity.CharP.ArithmeticBase

/-!
# The actual small arithmetic coefficient base

The image of `k[X]_(X)` under the chart `X ↦ π` is an actual DVR subring
of the ambient field. For the prime field in characteristic p it is exactly
`𝔽_p[π]_(π)`, and lies in every source stalk containing π, even when the
larger model DVR lies outside those stalks.
-/

noncomputable section
namespace HereditaryAtomicity.DVRBase
open scoped NNReal Polynomial
variable {k K : Type*} [Field k] [Field K] [Algebra k K]

/-- The literal image of `k[X]_(X)` at a specified transcendental coordinate. -/
def arithmeticCoefficientRing (π : K) (hπ : Transcendental k π) : Subring K :=
  let := CharP.FunctionField.rationalAlgebra π hπ
  (CharP.arithmeticBase k).toSubring.map (algebraMap (RatFunc k) K)

/-- The arithmetic base embeds isomorphically into its actual image. -/
def arithmeticCoefficientEquiv (π : K) (hπ : Transcendental k π) :
    CharP.arithmeticBase k ≃+* arithmeticCoefficientRing π hπ :=
  let := CharP.FunctionField.rationalAlgebra π hπ
  (CharP.arithmeticBase k).toSubring.equivMapOfInjective
    (algebraMap (RatFunc k) K) (algebraMap (RatFunc k) K).injective

instance arithmeticCoefficientRing_dvr (π : K) (hπ : Transcendental k π) :
    IsDiscreteValuationRing (arithmeticCoefficientRing π hπ) :=
  IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing (arithmeticCoefficientEquiv π hπ)

/-- The chosen coordinate itself, as uniformizer of the actual small base. -/
def arithmeticCoefficientUniformizer (π : K) (hπ : Transcendental k π) :
    arithmeticCoefficientRing π hπ :=
  arithmeticCoefficientEquiv π hπ (CharP.arithmeticUniformizer k)

@[simp] theorem arithmeticCoefficientUniformizer_coe (π : K) (hπ : Transcendental k π) :
    (arithmeticCoefficientUniformizer π hπ : K) = π :=
  CharP.arithmeticUniformizer_coordinate_image π hπ

theorem arithmeticCoefficientUniformizer_irreducible (π : K) (hπ : Transcendental k π) :
    Irreducible (arithmeticCoefficientUniformizer π hπ) :=
  (MulEquiv.irreducible_iff (f := (arithmeticCoefficientEquiv π hπ).toMulEquiv)).mpr (CharP.arithmeticUniformizer_irreducible k)

/-- A nonzero nonunit in a domain containing a field is transcendental over
that field. Applied to the model uniformizer, this constructs the chart. -/
theorem uniformizer_transcendental (O : Subring K) [Algebra k O]
    [IsScalarTower k O K] (π : O) (hπ : Irreducible π) :
    Transcendental k (π : K) := by
  apply (transcendental_algebraMap_iff (R := k) (S := O) (A := K) Subtype.val_injective).mpr
  intro halg
  exact hπ.not_isUnit (halg.isIntegral.isUnit hπ.ne_zero)

/-- The arithmetic coordinate base lies in any local ring containing the
constant field in which the chosen coordinate is in the maximal ideal.
The local ring need not have the ambient field as its own fraction field. -/
theorem arithmeticCoefficientRing_le_local
    (S : Subring K) [IsLocalRing S] [Algebra k S] [IsScalarTower k S K]
    (π : S) (hπ : Transcendental k (π : K))
    (hπM : π ∈ IsLocalRing.maximalIdeal S) :
    arithmeticCoefficientRing (π : K) hπ ≤ S := by
  let := CharP.FunctionField.polynomialAlgebra (k := k) (π : K)
  let := CharP.FunctionField.rationalAlgebra (π : K) hπ
  let := CharP.FunctionField.coordinate_scalarTower (π : K) hπ
  let : Algebra k[X] S := (Polynomial.aeval π).toRingHom.toAlgebra
  let : IsScalarTower k k[X] S := IsScalarTower.of_algebraMap_eq (fun c => by
    change algebraMap k S c = Polynomial.aeval π (algebraMap k k[X] c)
    simp)
  have hpoly (q : k[X]) :
      algebraMap (RatFunc k) K (algebraMap k[X] (RatFunc k) q) =
        (Polynomial.aeval π q : K) := by
    rw [← IsScalarTower.algebraMap_apply]
    change Polynomial.aeval (π : K) q = algebraMap S K (Polynomial.aeval π q)
    exact Polynomial.aeval_algHom_apply (IsScalarTower.toAlgHom k S K) π q
  rintro x ⟨a, ha, rfl⟩
  obtain ⟨f, g, hg, he⟩ := (CharP.mem_arithmeticBase_iff k a).mp ha
  rw [he, map_mul, map_inv₀, hpoly f, hpoly g]
  have hgM : Polynomial.aeval π g ∉ IsLocalRing.maximalIdeal S := by
    apply CharP.polynomial_image_not_mem_of_constantCoeff_ne_zero k S
      (IsLocalRing.maximalIdeal S) ?_ g hg
    change Polynomial.aeval π Polynomial.X ∈ IsLocalRing.maximalIdeal S
    simpa using hπM
  have hgu : IsUnit (Polynomial.aeval π g) := by
    simpa only [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not] using hgM
  obtain ⟨u, hu⟩ := hgu
  apply S.mul_mem (Polynomial.aeval π f).property
  rw [← hu]
  change (S.subtype (u : S))⁻¹ ∈ S
  rw [← map_units_inv S.subtype u]
  exact ((u⁻¹ : Sˣ) : S).property

/-- Every selected source prime containing the coordinate contains the same
actual arithmetic coefficient base in its field-valued localization. -/
theorem arithmeticCoefficientRing_le_ofPrime
    (D : Subring K) [IsFractionRing D K] [Algebra k D] [IsScalarTower k D K]
    (π : D) (hπ : Transcendental k (π : K))
    (M : Ideal D) [M.IsPrime] (hπM : π ∈ M) :
    arithmeticCoefficientRing (π : K) hπ ≤ (LocalSubring.ofPrime D M).toSubring := by
  let := CharP.FunctionField.rationalAlgebra (π : K) hπ
  rintro x ⟨a, ha, rfl⟩
  exact CharP.arithmeticBase_coordinate_image_mem_ofPrime k K D π hπ M hπM ⟨a, ha⟩


/-- A model uniformizer over a field of constants supplies the exact small
arithmetic DVR, its uniformizer, division closure, and simultaneous containment
in every source maximal stalk containing that same coordinate. -/
theorem exists_arithmetic_coefficient_base
    (D O : Subring K) [IsFractionRing D K] [IsDiscreteValuationRing O]
    [Algebra k D] [IsScalarTower k D K] [Algebra k O] [IsScalarTower k O K]
    (πD : D) (πO : O) (hπeq : (πD : K) = (πO : K)) (hπirr : Irreducible πO)
    (w : Valuation K ℝ≥0) (hO : ∀ a : O, w (a : K) ≤ 1)
    (hnorm : realValuationOrder w (πO : K) = 1) :
    ∃ (htr : Transcendental k (πO : K)) (B : Subring K) (πB : B) (hBO : B ≤ O),
      B = arithmeticCoefficientRing (πO : K) htr ∧ IsDiscreteValuationRing B ∧
      (πB : K) = (πO : K) ∧ Irreducible πB ∧
      Irreducible (Subring.inclusion hBO πB) ∧
      UniformizerDivisionClosed B πB w ∧
      (∀ b : B, w (b : K) ≤ 1) ∧
      ∀ M : MaximalSpectrum D, πD ∈ M.asIdeal →
        B ≤ (LocalSubring.ofPrime D M.asIdeal).toSubring := by
  let htr := uniformizer_transcendental (k := k) O πO hπirr
  let B := arithmeticCoefficientRing (πO : K) htr
  let πB : B := arithmeticCoefficientUniformizer (πO : K) htr
  have hBO : B ≤ O := arithmeticCoefficientRing_le_local O πO htr
    (by simpa only [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] using hπirr.not_isUnit)
  have hπB : (πB : K) = (πO : K) := arithmeticCoefficientUniformizer_coe _ _
  have hirr : Irreducible πB := arithmeticCoefficientUniformizer_irreducible _ _
  have hB : ∀ b : B, w (b : K) ≤ 1 := fun b => hO ⟨b, hBO b.property⟩
  have hnormB : realValuationOrder w (πB : K) = 1 := hπB ▸ hnorm
  refine ⟨htr, B, πB, hBO, rfl, inferInstance, hπB, hirr, ?_,
    uniformizerDivisionClosed_of_dvr B πB hirr w hB hnormB, hB, ?_⟩
  · have he : Subring.inclusion hBO πB = πO := Subtype.ext hπB
    exact he.symm ▸ hπirr
  · intro M hM
    have htrD : Transcendental k (πD : K) := hπeq ▸ htr
    have hle := arithmeticCoefficientRing_le_ofPrime D πD htrD M.asIdeal hM
    simpa only [hπeq] using hle

/-- The characteristic-p base used by the coefficient transfer is exactly the image
`𝔽_p[X]_(X)` with `X ↦ π`, and all its required containments and division closure are
proved from the original uniformizer and source-stalk hypotheses. No
containment of the larger DVR in the original source or its stalks is assumed. -/
theorem exists_primeField_coefficient_base
    (p : ℕ) [Fact p.Prime] [CharP K p]
    (D O : Subring K) [IsFractionRing D K] [IsDiscreteValuationRing O]
    (πD : D) (πO : O) (hπeq : (πD : K) = (πO : K)) (hπirr : Irreducible πO)
    (w : Valuation K ℝ≥0) (hO : ∀ a : O, w (a : K) ≤ 1)
    (hnorm : realValuationOrder w (πO : K) = 1) :
    letI := ZMod.algebra K p
    ∃ (htr : Transcendental (ZMod p) (πO : K)) (B : Subring K) (πB : B) (hBO : B ≤ O),
      B = arithmeticCoefficientRing (πO : K) htr ∧ IsDiscreteValuationRing B ∧
      (πB : K) = (πO : K) ∧ Irreducible πB ∧
      Irreducible (Subring.inclusion hBO πB) ∧
      UniformizerDivisionClosed B πB w ∧
      (∀ b : B, w (b : K) ≤ 1) ∧
      ∀ M : MaximalSpectrum D, πD ∈ M.asIdeal →
        B ≤ (LocalSubring.ofPrime D M.asIdeal).toSubring := by
  let : Algebra (ZMod p) K := ZMod.algebra K p
  let : CharP D p := D.subtype.charP D.subtype_injective p
  let : CharP O p := O.subtype.charP O.subtype_injective p
  let : Algebra (ZMod p) D := ZMod.algebra D p
  let : Algebra (ZMod p) O := ZMod.algebra O p
  let : SMul (ZMod p) D := (inferInstance : Algebra (ZMod p) D).toSMul
  let : SMul (ZMod p) O := (inferInstance : Algebra (ZMod p) O).toSMul
  let : IsScalarTower (ZMod p) D K := IsScalarTower.of_algebraMap_eq fun a =>
    RingHom.congr_fun (Subsingleton.elim (algebraMap (ZMod p) K)
      ((algebraMap D K).comp (algebraMap (ZMod p) D))) a
  let : IsScalarTower (ZMod p) O K := IsScalarTower.of_algebraMap_eq fun a =>
    RingHom.congr_fun (Subsingleton.elim (algebraMap (ZMod p) K)
      ((algebraMap O K).comp (algebraMap (ZMod p) O))) a
  exact exists_arithmetic_coefficient_base (k := ZMod p) D O πD πO hπeq hπirr w hO hnorm

end HereditaryAtomicity.DVRBase
