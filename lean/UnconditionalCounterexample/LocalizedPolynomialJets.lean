import Mathlib.Algebra.DualNumber
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.RingTheory.Localization.Basic
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Polynomial first jets and their localization

The first jet is the actual pair of a polynomial's value and evaluated formal
first derivative. Nonvanishing localization denominators make these jets units,
so the first-jet map extends to the actual polynomial localization. No fraction
field identification or topological completion is required.

The same nonvanishing conditions make denominators units modulo every power of
the polynomial vanishing at two retained points. This supplies the exact
quotient-representative hypothesis in the localized conductor argument.
-/

namespace UnconditionalCounterexample.LocalizedPolynomialJets

open Polynomial

section Polynomial

variable {K : Type*} [CommRing K]

/-- Actual value and formal derivative at a point, assembled as an algebra map. -/
noncomputable def firstJet (a : K) : K[X] →ₐ[K] DualNumber K where
  toFun f := ⟨f.eval a, f.derivative.eval a⟩
  map_zero' := by ext <;> simp
  map_one' := by ext <;> simp
  map_add' f g := by
    apply TrivSqZeroExt.ext
    · change (f + g).eval a = f.eval a + g.eval a
      simp
    · change (f + g).derivative.eval a = f.derivative.eval a + g.derivative.eval a
      simp
  map_mul' f g := by
    apply TrivSqZeroExt.ext
    · change (f * g).eval a = f.eval a * g.eval a
      simp
    · change (f * g).derivative.eval a =
        f.eval a * g.derivative.eval a + f.derivative.eval a * g.eval a
      simp [derivative_mul, add_comm]
  commutes' c := by
    apply TrivSqZeroExt.ext
    · change (C c).eval a = c
      simp
    · change (C c).derivative.eval a = 0
      simp

@[simp] theorem firstJet_fst (a : K) (f : K[X]) :
    (firstJet a f).fst = f.eval a := rfl

@[simp] theorem firstJet_snd (a : K) (f : K[X]) :
    (firstJet a f).snd = f.derivative.eval a := rfl

@[simp] theorem firstJet_C (a c : K) :
    firstJet a (C c) = algebraMap K (DualNumber K) c :=
  (firstJet a).commutes c

@[simp] theorem firstJet_X (a : K) :
    firstJet a X = (a, 1) := by ext <;> simp

end Polynomial

section Localization

variable {K : Type*} [Field K] (M : Submonoid K[X])
    (A : Type*) [CommRing A] [Algebra K[X] A] [IsLocalization M A]
    (a : K) (hnonzero : ∀ m : M, (m : K[X]).eval a ≠ 0)

/-- First jets on an actual localization, defined when every denominator
is nonzero at the retained point. -/
noncomputable def localizedFirstJet : A →+* DualNumber K :=
  IsLocalization.lift (M := M) (g := (firstJet a).toRingHom) (fun m =>
    TrivSqZeroExt.isUnit_iff_isUnit_fst.mpr ((hnonzero m).isUnit))

@[simp] theorem localizedFirstJet_algebraMap (f : K[X]) :
    localizedFirstJet M A a hnonzero (algebraMap K[X] A f) = firstJet a f :=
  IsLocalization.lift_eq _ f

@[simp] theorem localizedFirstJet_algebraMap_fst (f : K[X]) :
    (localizedFirstJet M A a hnonzero (algebraMap K[X] A f)).fst = f.eval a := by
  rw [localizedFirstJet_algebraMap, firstJet_fst]

@[simp] theorem localizedFirstJet_algebraMap_snd (f : K[X]) :
    (localizedFirstJet M A a hnonzero (algebraMap K[X] A f)).snd =
      f.derivative.eval a := by
  rw [localizedFirstJet_algebraMap, firstJet_snd]

@[simp] theorem localizedFirstJet_C (c : K) :
    localizedFirstJet M A a hnonzero (algebraMap K[X] A (C c)) =
      algebraMap K (DualNumber K) c := by
  rw [localizedFirstJet_algebraMap, firstJet_C]

/-- The first jet of an actual localized fraction is the quotient of its jets. -/
theorem localizedFirstJet_mk' (f : K[X]) (m : M) :
    localizedFirstJet M A a hnonzero (IsLocalization.mk' A f m) =
      firstJet a f * (firstJet a (m : K[X]))⁻¹ := by
  apply (IsLocalization.lift_mk'_spec _ f _ m).mpr
  change firstJet a f = firstJet a (m : K[X]) *
    (firstJet a f * (firstJet a (m : K[X]))⁻¹)
  rw [mul_left_comm, TrivSqZeroExt.mul_inv_cancel
    (x := firstJet a (m : K[X])) (hnonzero m), mul_one]

theorem localizedFirstJet_mk'_fst (f : K[X]) (m : M) :
    (localizedFirstJet M A a hnonzero (IsLocalization.mk' A f m)).fst =
      f.eval a / (m : K[X]).eval a := by
  rw [localizedFirstJet_mk', TrivSqZeroExt.fst_mul, TrivSqZeroExt.fst_inv]
  simp only [firstJet_fst, div_eq_mul_inv]

/-- The derivative coordinate on fractions satisfies the ordinary quotient rule. -/
theorem localizedFirstJet_mk'_snd (f : K[X]) (m : M) :
    (localizedFirstJet M A a hnonzero (IsLocalization.mk' A f m)).snd =
      (f.derivative.eval a * (m : K[X]).eval a -
        f.eval a * (m : K[X]).derivative.eval a) / ((m : K[X]).eval a) ^ 2 := by
  rw [localizedFirstJet_mk', DualNumber.snd_mul]
  change f.eval a * -(((m : K[X]).eval a)⁻¹ * (m : K[X]).derivative.eval a *
    ((m : K[X]).eval a)⁻¹) + f.derivative.eval a * ((m : K[X]).eval a)⁻¹ = _
  field_simp [hnonzero m]
  ring

theorem localizedFirstJet_fst_add (x y : A) :
    (localizedFirstJet M A a hnonzero (x + y)).fst =
      (localizedFirstJet M A a hnonzero x).fst +
        (localizedFirstJet M A a hnonzero y).fst := by
  rw [map_add, TrivSqZeroExt.fst_add]

theorem localizedFirstJet_snd_add (x y : A) :
    (localizedFirstJet M A a hnonzero (x + y)).snd =
      (localizedFirstJet M A a hnonzero x).snd +
        (localizedFirstJet M A a hnonzero y).snd := by
  rw [map_add, TrivSqZeroExt.snd_add]

theorem localizedFirstJet_fst_mul (x y : A) :
    (localizedFirstJet M A a hnonzero (x * y)).fst =
      (localizedFirstJet M A a hnonzero x).fst *
        (localizedFirstJet M A a hnonzero y).fst := by
  rw [map_mul, TrivSqZeroExt.fst_mul]

/-- The derivative coordinate obeys the actual Leibniz rule on the localization. -/
theorem localizedFirstJet_snd_mul (x y : A) :
    (localizedFirstJet M A a hnonzero (x * y)).snd =
      (localizedFirstJet M A a hnonzero x).fst *
          (localizedFirstJet M A a hnonzero y).snd +
        (localizedFirstJet M A a hnonzero x).snd *
          (localizedFirstJet M A a hnonzero y).fst := by
  rw [map_mul, DualNumber.snd_mul]

@[simp] theorem localizedFirstJet_scalar [Algebra K A] [IsScalarTower K K[X] A]
    (c : K) :
    localizedFirstJet M A a hnonzero (algebraMap K A c) =
      algebraMap K (DualNumber K) c := by
  rw [IsScalarTower.algebraMap_apply K K[X] A c]
  exact localizedFirstJet_C M A a hnonzero c

end Localization

/-- Nonvanishing at a point means coprimality with its linear polynomial. -/
theorem isCoprime_X_sub_C_of_eval_ne_zero
    {K : Type*} [Field K] (f : K[X]) (a : K) (ha : f.eval a ≠ 0) :
    IsCoprime (X - C a) f := by
  apply (Polynomial.prime_X_sub_C a).irreducible.coprime_iff_not_dvd.mpr
  exact fun h => ha (Polynomial.dvd_iff_isRoot.mp h)

/-- Nonvanishing at both retained points makes every denominator a unit modulo
every power of their vanishing polynomial, including exponent zero. -/
theorem isUnit_quotient_pair_pow_of_eval_ne_zero
    {K : Type*} [Field K] (f : K[X]) (a b : K) (k : ℕ)
    (ha : f.eval a ≠ 0) (hb : f.eval b ≠ 0) :
    IsUnit (Ideal.Quotient.mk
      (Ideal.span {((X - C a) * (X - C b)) ^ k}) f) := by
  have hcop : IsCoprime (((X - C a) * (X - C b)) ^ k) f :=
    ((isCoprime_X_sub_C_of_eval_ne_zero f a ha).mul_left
      (isCoprime_X_sub_C_of_eval_ne_zero f b hb)).pow_left
  have hzero : Ideal.Quotient.mk
      (Ideal.span {((X - C a) * (X - C b)) ^ k})
      (((X - C a) * (X - C b)) ^ k) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
  have hm := hcop.map (Ideal.Quotient.mk
    (Ideal.span {((X - C a) * (X - C b)) ^ k}))
  rw [hzero] at hm
  exact isCoprime_zero_left.mp hm

end UnconditionalCounterexample.LocalizedPolynomialJets
