import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.RingTheory.Ideal.Int
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra

/-!
# Localization and p-adic scalar extension
-/

noncomputable section

namespace UnconditionalCounterexample.LocalAlgebra.PadicLocalization

variable (p : ℕ) [Fact p.Prime]

/-- The prime ideal `(p)` of the ordinary integers. -/
abbrev primeIdeal : Ideal ℤ := Ideal.span {(p : ℤ)}

/-- The ordinary integers localized at `(p)`. -/
abbrev IntegerLocalization := Localization.AtPrime (primeIdeal p)

/-- An integer avoiding `(p)` is a unit in the actual p-adic integers. -/
theorem intCast_isUnit_of_not_mem (z : ℤ) (hz : z ∉ primeIdeal p) :
    IsUnit (z : ℤ_[p]) := by
  classical
  by_contra h
  apply hz
  apply Ideal.mem_span_singleton.mpr
  exact (PadicInt.norm_int_lt_one_iff_dvd z).mp (PadicInt.not_isUnit_iff.mp h)

/-- The exact integer-unit test for finite conductor support arguments. -/
theorem intCast_isUnit_iff (z : ℤ) :
    IsUnit (z : ℤ_[p]) ↔ ¬(p : ℤ) ∣ z := by
  constructor
  · intro hz hdiv
    exact (PadicInt.not_isUnit_iff.mpr
      ((PadicInt.norm_int_lt_one_iff_dvd z).mpr hdiv)) hz
  · intro hz
    apply intCast_isUnit_of_not_mem p z
    simpa only [primeIdeal, Ideal.mem_span_singleton] using hz

/-- The canonical localization map into the p-adic integers. -/
def toPadicInt : IntegerLocalization p →+* ℤ_[p] :=
  IsLocalization.lift (M := (primeIdeal p).primeCompl)
    (g := algebraMap ℤ ℤ_[p]) (fun z => intCast_isUnit_of_not_mem p z z.property)

@[simp]
theorem toPadicInt_algebraMap (z : ℤ) :
    toPadicInt p (algebraMap ℤ (IntegerLocalization p) z) = (z : ℤ_[p]) :=
  IsLocalization.lift_eq _ z

instance padicIntAlgebra : Algebra (IntegerLocalization p) ℤ_[p] :=
  (toPadicInt p).toAlgebra

instance padicIntScalarTower :
    letI : SMul ℤ (IntegerLocalization p) := Algebra.toSMul
    IsScalarTower ℤ (IntegerLocalization p) ℤ_[p] := by
  let : SMul ℤ (IntegerLocalization p) := Algebra.toSMul
  constructor
  intro r s x
  simp only [Algebra.smul_def, map_mul]
  change (toPadicInt p (algebraMap ℤ (IntegerLocalization p) r) * toPadicInt p s) * x =
    (r : ℤ_[p]) * (toPadicInt p s * x)
  rw [toPadicInt_algebraMap, mul_assoc]

/-- The canonical map reflects units and hence is a local ring homomorphism. -/
instance toPadicInt_isLocalHom : IsLocalHom (toPadicInt p) where
  map_nonunit := by
    intro x hx
    obtain ⟨r, s, rfl⟩ := IsLocalization.exists_mk'_eq (primeIdeal p).primeCompl x
    apply (IsLocalization.AtPrime.isUnit_mk'_iff (IntegerLocalization p)
      (primeIdeal p) r s).mpr
    intro hr
    have heq := congrArg (toPadicInt p)
      (IsLocalization.mk'_spec (IntegerLocalization p) r s)
    have hur : IsUnit (r : ℤ_[p]) := by
      rw [map_mul, toPadicInt_algebraMap, toPadicInt_algebraMap] at heq
      rw [← heq]
      exact hx.mul (intCast_isUnit_of_not_mem p s s.property)
    have hlt : ‖(r : ℤ_[p])‖ < 1 :=
      (PadicInt.norm_int_lt_one_iff_dvd r).mpr (Ideal.mem_span_singleton.mp hr)
    exact (PadicInt.not_isUnit_iff.mpr hlt) hur

instance padicIntAlgebra_isLocalHom :
    IsLocalHom (algebraMap (IntegerLocalization p) ℤ_[p]) :=
  toPadicInt_isLocalHom p

/-- Torsion-freeness over the integers supplies flatness after localization. -/
instance padicIntFlat : Module.Flat (IntegerLocalization p) ℤ_[p] := by
  exact (Module.flat_iff_of_isLocalization (IntegerLocalization p)
    (primeIdeal p).primeCompl ℤ_[p]).mpr inferInstance

/-- Completion at `(p)` is faithfully flat over the localized integers. -/
instance padicIntFaithfullyFlat :
    Module.FaithfullyFlat (IntegerLocalization p) ℤ_[p] :=
  Module.FaithfullyFlat.of_flat_of_isLocalHom

end UnconditionalCounterexample.LocalAlgebra.PadicLocalization
