import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.Field.ZMod
import Mathlib.RingTheory.Valuation.Basic
import Mathlib.Basic.NNReal.Basic

/-!
# Coefficient rings for finite-branch conductor cuts

Unit values are forced by actual containment of a coefficient ring in all
valuation rings. A DVR coefficient has the same natural exponent at every branch.
-/

open scoped NNReal

noncomputable section

namespace HereditaryAtomicity

universe u v w

/-- A valuation bounded by one on a ring takes value one on every ring unit. -/
theorem coefficient_unit_value
    {A : Type u} [CommRing A] {K : Type v} [Field K]
    (f : A →+* K) (v : Valuation K ℝ≥0)
    (hv : ∀ a : A, v (f a) ≤ 1) {a : A} (ha : IsUnit a) :
    v (f a) = 1 := by
  obtain ⟨u, rfl⟩ := ha
  apply le_antisymm (hv _)
  calc
    1 = v (f (u : A)) * v (f ((u⁻¹ : Aˣ) : A)) := by
      rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
    _ ≤ v (f (u : A)) * 1 := mul_le_mul_of_nonneg_left (hv _) zero_le
    _ = v (f (u : A)) := mul_one _

/-- Every nonzero coefficient from a field has value one at every containing valuation. -/
theorem field_coefficient_value
    {k : Type u} [Field k] {K : Type v} [Field K]
    (f : k →+* K) (v : Valuation K ℝ≥0)
    (hv : ∀ a : k, v (f a) ≤ 1) {a : k} (ha : a ≠ 0) :
    v (f a) = 1 :=
  coefficient_unit_value f v hv (isUnit_iff_ne_zero.mpr ha)

/-- The exponent of a nonzero DVR coefficient is common to all containing valuations. -/
theorem dvr_coefficient_values
    {A : Type u} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    {K : Type v} [Field K] {ι : Type w}
    (f : A →+* K) (v : ι → Valuation K ℝ≥0)
    (hv : ∀ i a, v i (f a) ≤ 1) {π a : A}
    (hπ : Irreducible π) (ha : a ≠ 0) :
    ∃ n : ℕ, ∀ i, v i (f a) = v i (f π) ^ n := by
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hπ
  refine ⟨n, fun i => ?_⟩
  rw [map_mul, map_pow, map_mul, map_pow,
    coefficient_unit_value f (v i) (hv i) u.isUnit, one_mul]

/-- The prime of the integers selected by the residue field of a local ring. -/
def intResiduePrime (R : Type u) [CommRing R] [IsLocalRing R] : Ideal ℤ :=
  RingHom.ker ((IsLocalRing.residue R).comp (Int.castRingHom R))

instance intResiduePrime_isPrime (R : Type u)
    [CommRing R] [IsLocalRing R] : (intResiduePrime R).IsPrime :=
  RingHom.ker_isPrime _

/-- Denominators outside the residue kernel of the integers are units in a local ring. -/
theorem int_residue_kernel_denominator_unit
    (R : Type u) [CommRing R] [IsLocalRing R]
    (s : (intResiduePrime R).primeCompl) :
    IsUnit ((s : ℤ) : R) := by
  apply (IsLocalRing.residue_ne_zero_iff_isUnit _).mp
  exact s.property

/-- The canonical localization of the integers at the residue kernel maps into the local ring. -/
def integerLocalCoefficientMap
    (R : Type u) [CommRing R] [IsLocalRing R] :
    Localization.AtPrime (intResiduePrime R) →+* R :=
  IsLocalization.lift (g := Int.castRingHom R) (int_residue_kernel_denominator_unit R)

@[simp] theorem integerLocalCoefficientMap_int
    (R : Type u) [CommRing R] [IsLocalRing R] (n : ℤ) :
    integerLocalCoefficientMap R (algebraMap ℤ _ n) = (n : R) := by
  exact IsLocalization.lift_eq (int_residue_kernel_denominator_unit R) n

/-- The integer coefficient localization reflects units of the local target. -/
instance integerLocalCoefficientMap_isLocalHom
    (R : Type u) [CommRing R] [IsLocalRing R] :
    IsLocalHom (integerLocalCoefficientMap R) where
  map_nonunit x hx := by
    let P := intResiduePrime R
    let A := Localization.AtPrime P
    obtain ⟨⟨a, s⟩, hxs⟩ := IsLocalization.surj P.primeCompl x
    have heq : integerLocalCoefficientMap R x * (s : ℤ) = (a : R) := by
      simpa only [map_mul, integerLocalCoefficientMap_int] using
        congrArg (integerLocalCoefficientMap R) hxs
    have ha : IsUnit (a : R) := heq ▸ hx.mul (int_residue_kernel_denominator_unit R s)
    have haP : a ∈ P.primeCompl := (IsLocalRing.residue_ne_zero_iff_isUnit _).mpr ha
    have haA : IsUnit (algebraMap ℤ A a) := IsLocalization.map_units A ⟨a, haP⟩
    exact isUnit_of_mul_isUnit_left (hxs.symm ▸ haA)

/-- In characteristic zero the actual integer coefficient map is injective. -/
theorem integerLocalCoefficientMap_injective
    (R : Type u) [CommRing R] [IsLocalRing R] [CharZero R] :
    Function.Injective (integerLocalCoefficientMap R) := by
  rw [integerLocalCoefficientMap, IsLocalization.lift_injective_iff]
  intro a b
  rw [(IsLocalization.injective (Localization.AtPrime (intResiduePrime R))
    (intResiduePrime R).primeCompl_le_nonZeroDivisors).eq_iff,
    ]
  change a = b ↔ (a : R) = (b : R)
  exact Int.cast_injective.eq_iff.symm

/-- At a nonzero residue prime the integer coefficient localization is a DVR. -/
theorem integerLocalCoefficient_isDiscreteValuationRing
    (R : Type u) [CommRing R] [IsLocalRing R]
    (hP : intResiduePrime R ≠ ⊥) :
    IsDiscreteValuationRing (Localization.AtPrime (intResiduePrime R)) :=
  IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain ℤ hP _

/-- At the zero residue prime the integer coefficient localization is a field. -/
theorem integerLocalCoefficient_isField
    (R : Type u) [CommRing R] [IsLocalRing R]
    (hP : intResiduePrime R = ⊥) :
    IsField (Localization.AtPrime (intResiduePrime R)) := by
  let P := intResiduePrime R
  let A := Localization.AtPrime P
  refine ⟨⟨0, 1, zero_ne_one⟩, mul_comm, ?_⟩
  intro x hx
  obtain ⟨a, s, rfl⟩ := IsLocalization.exists_mk'_eq P.primeCompl x
  have ha : a ≠ 0 := by
    intro ha
    apply hx
    simp [ha]
  have hau : IsUnit (IsLocalization.mk' A a s) := by
    apply (IsLocalization.AtPrime.isUnit_mk'_iff A P a s).mpr
    simpa only [P, hP, Ideal.mem_primeCompl_iff, Ideal.mem_bot] using ha
  exact isUnit_iff_exists_inv.mp hau

/-- Every local domain contains either a field or a DVR whose nonunits stay nonunits.
The coefficient ring is a literal unital subring of the source. -/
theorem exists_field_or_dvr_coefficients
    (R : Type u) [CommRing R] [IsDomain R] [IsLocalRing R] :
    ∃ A : Subring R, IsField A ∨
      (IsDiscreteValuationRing A ∧ IsLocalHom A.subtype) := by
  classical
  rcases CharP.char_is_prime_or_zero R (ringChar R) with hp | hp
  · let : Fact (Nat.Prime (ringChar R)) := ⟨hp⟩
    let f : ZMod (ringChar R) →+* R := ZMod.castHom (dvd_refl _) R
    let e := RingEquiv.ofBijective f.rangeRestrict ⟨fun _ _ h => f.injective (congrArg Subtype.val h), f.rangeRestrict_surjective⟩
    exact ⟨f.range, Or.inl (e.symm.toMulEquiv.isField (Field.toIsField _))⟩
  · let : CharP R 0 := hp ▸ inferInstance
    let : CharZero R := CharP.charP_to_charZero R
    let f := integerLocalCoefficientMap R
    let e := RingEquiv.ofBijective f.rangeRestrict ⟨fun _ _ h => integerLocalCoefficientMap_injective R (congrArg Subtype.val h), f.rangeRestrict_surjective⟩
    refine ⟨f.range, ?_⟩
    by_cases hP : intResiduePrime R = ⊥
    · exact Or.inl (e.symm.toMulEquiv.isField (integerLocalCoefficient_isField R hP))
    · let : IsDiscreteValuationRing (Localization.AtPrime (intResiduePrime R)) :=
        integerLocalCoefficient_isDiscreteValuationRing R hP
      refine Or.inr ⟨IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing e, ?_⟩
      constructor
      intro x hx
      obtain ⟨a, rfl⟩ := e.surjective x
      apply e.toRingHom.isUnit_map
      exact (isUnit_map_iff f a).mp hx

end HereditaryAtomicity
