import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.GroupTheory.MonoidLocalization.Maps

/-!
# Extending local component classes to the fraction field

A multiplicative map from the nonzero elements of a domain to an abelian group extends
uniquely to the nonzero elements of its fraction field.
-/
noncomputable section
namespace HereditaryAtomicity.DVRBase
open scoped nonZeroDivisors
variable {R K G : Type*} [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K] [CommGroup G]

/-- The canonical embedding of nonzero source elements into fraction units. -/
def sourceNonzeroToFractionUnits : R⁰ →* Kˣ where
  toFun a := Units.mk0 (algebraMap R K a)
    ((map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr
      (nonZeroDivisors.ne_zero a.property))
  map_one' := by ext; simp
  map_mul' a b := by ext; simp

/-- Fraction units are the group completion of the nonzero source monoid. -/
def fractionUnitsLocalization : (⊤ : Submonoid R⁰).LocalizationMap Kˣ where
  toFun := sourceNonzeroToFractionUnits
  map_mul' := sourceNonzeroToFractionUnits.map_mul
  isLocalizationMap := {
    map_units := fun _ => Group.isUnit _
    surj := by
      intro z
      obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective R (z : K)
      have ha : a ≠ 0 := by
        intro ha
        simp [ha] at hab
        exact z.ne_zero hab.symm
      refine ⟨(⟨a, mem_nonZeroDivisors_iff_ne_zero.mpr ha⟩,
        ⟨⟨b, hb⟩, Submonoid.mem_top _⟩), ?_⟩
      apply Units.ext
      change (z : K) * algebraMap R K b = algebraMap R K a
      exact ((div_eq_iff ((map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr
        (nonZeroDivisors.ne_zero hb))).mp hab).symm
    exists_of_eq := by
      intro a b h
      have he : a = b := by
        apply Subtype.ext
        apply IsFractionRing.injective R K
        exact congrArg (fun z : Kˣ => (z : K)) h
      exact ⟨1, by simpa using he⟩ }

/-- Extend a nonzero-source class homomorphism to all fraction units. -/
def extendSourceClassHom (φ : R⁰ →* G) : Kˣ →* G :=
  (fractionUnitsLocalization (R := R) (K := K)).lift (fun _ => Group.isUnit _)
    (g := φ)

@[simp] theorem extendSourceClassHom_source (φ : R⁰ →* G) (a : R⁰) :
    extendSourceClassHom (K := K) φ (sourceNonzeroToFractionUnits a) = φ a :=
  (fractionUnitsLocalization (R := R) (K := K)).lift_eq (fun _ => Group.isUnit _) a

/-- The extension is uniquely determined by its values on nonzero source elements. -/
theorem extendSourceClassHom_unique (φ : R⁰ →* G) (ψ : Kˣ →* G)
    (hψ : ∀ a, ψ (sourceNonzeroToFractionUnits a) = φ a) :
    extendSourceClassHom (K := K) φ = ψ :=
  (fractionUnitsLocalization (R := R) (K := K)).lift_unique (fun _ => Group.isUnit _) hψ

/-- The extended class of a literal source fraction is the quotient of the
classes of numerator and denominator. -/
theorem extendSourceClassHom_div (φ : R⁰ →* G) (a b : R⁰) :
    extendSourceClassHom (K := K) φ
      (sourceNonzeroToFractionUnits a / sourceNonzeroToFractionUnits b) = φ a / φ b := by
  simp

end HereditaryAtomicity.DVRBase
