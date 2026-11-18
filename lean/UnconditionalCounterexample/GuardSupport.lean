import UnconditionalCounterexample.EvaluationDVR
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.RingTheory.Localization.Integral
import Mathlib.Tactic

/-!
# Finite guard support from enumerated polynomial avoidance

Fix an enumeration of all nonzero integer polynomials. A guard assigned at stage i
avoids the first i entries. If each initial set of stages has finite preimage, every
fixed polynomial has finite guard support.

These hypotheses are stronger finite exclusions than the source schedule
listing earlier raw factors. Their construction needs a one-stage cutoff
lookahead controlling leading coefficients and degrees of the next prefix.
This module proves neither that successor nor the source logarithmic estimate.

Actual p-adic reduction detects units. Clearing coefficients then gives finite
nontrivial valuation support for every nonzero element of RatFunc Rat, using
the existing transcendental evaluation embedding. No prime-degree hypothesis
is needed.
-/

namespace UnconditionalCounterexample.GuardSupport

open Polynomial

theorem padicInt_isUnit_iff_toZMod_ne_zero {p : ℕ} [Fact p.Prime] (x : ℤ_[p]) :
    IsUnit x ↔ PadicInt.toZMod x ≠ 0 := by
  rw [← not_iff_not]
  simp only [not_not, ← RingHom.mem_ker, PadicInt.ker_toZMod,
    IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]

theorem intPolynomial_eval_unit_of_residue_nonzero {p : ℕ} [Fact p.Prime]
    (U : ℤ[X]) (β : ℤ_[p])
    (h : U.eval₂ (Int.castRingHom (ZMod p)) (PadicInt.toZMod β) ≠ 0) :
    IsUnit (U.eval₂ (Int.castRingHom ℤ_[p]) β) := by
  apply (padicInt_isUnit_iff_toZMod_ne_zero _).mpr
  rw [Polynomial.hom_eval₂]
  have hc : PadicInt.toZMod.comp (Int.castRingHom ℤ_[p]) =
      Int.castRingHom (ZMod p) := Subsingleton.elim _ _
  simpa only [hc] using h

/-- Rational primes indexing the guard evaluations. -/
abbrev PrimeIndex := {p : ℕ // p.Prime}

/-- Expose primality to the p-adic type constructors. -/
instance primeFact (p : PrimeIndex) : Fact p.val.Prime := ⟨p.property⟩

/-- Every nonzero integer polynomial, including nonzero constants. -/
abbrev NonzeroIntPolynomial := {U : ℤ[X] // U ≠ 0}

theorem exists_nonzeroIntPolynomial_enumeration :
    ∃ U : ℕ → NonzeroIntPolynomial, Function.Surjective U := by
  have : Countable ℤ[X] := (Polynomial.toFinsuppIso ℤ).injective.countable
  let : Nonempty NonzeroIntPolynomial := ⟨⟨1, one_ne_zero⟩⟩
  exact exists_surjective_nat NonzeroIntPolynomial

/-- Fix the countable list before beginning the stage recursion. -/
noncomputable def integerPolynomialEnumeration : ℕ → NonzeroIntPolynomial :=
  exists_nonzeroIntPolynomial_enumeration.choose

theorem integerPolynomialEnumeration_surjective :
    Function.Surjective integerPolynomialEnumeration :=
  exists_nonzeroIntPolynomial_enumeration.choose_spec

/-- Once its enumeration index has been passed, an integer polynomial is a
unit at every new guard. Earlier guards form a finite exceptional set. -/
theorem intPolynomial_nonunit_finite
    (U : ℕ → NonzeroIntPolynomial) (hU : Function.Surjective U)
    (stage : PrimeIndex → ℕ) (hstage : ∀ n, {p | stage p ≤ n}.Finite)
    (β : (p : PrimeIndex) → ℤ_[p.val])
    (havoid : ∀ p j, j < stage p →
      (U j).val.eval₂ (Int.castRingHom (ZMod p.val)) (PadicInt.toZMod (β p)) ≠ 0)
    (V : ℤ[X]) (hV : V ≠ 0) :
    {p : PrimeIndex | ¬ IsUnit (V.eval₂ (Int.castRingHom ℤ_[p.val]) (β p))}.Finite := by
  obtain ⟨j, hj⟩ := hU ⟨V, hV⟩
  apply (hstage j).subset
  intro p hp
  change stage p ≤ j
  by_contra hn
  have hjp : j < stage p := by omega
  apply hp
  apply intPolynomial_eval_unit_of_residue_nonzero
  have hav := havoid p j hjp
  simpa only [hj] using hav

theorem coe_intPolynomial_eval {p : ℕ} [Fact p.Prime] (V : ℤ[X]) (β : ℤ_[p]) :
    ((V.eval₂ (Int.castRingHom ℤ_[p]) β : ℤ_[p]) : ℚ_[p]) =
      V.eval₂ (Int.castRingHom ℚ_[p]) (β : ℚ_[p]) := by
  change (algebraMap ℤ_[p] ℚ_[p]) (V.eval₂ (Int.castRingHom ℤ_[p]) β) = _
  rw [Polynomial.hom_eval₂]
  have hc : (algebraMap ℤ_[p] ℚ_[p]).comp (Int.castRingHom ℤ_[p]) =
      Int.castRingHom ℚ_[p] := Subsingleton.elim _ _
  rw [hc]
  rfl

/-- Clear the coefficients of a nonzero rational polynomial. -/
theorem exists_integer_multiple (f : ℚ[X]) (hf : f ≠ 0) :
    ∃ (d : ℤ) (V : ℤ[X]), d ≠ 0 ∧ V ≠ 0 ∧
      V.map (algebraMap ℤ ℚ) = Polynomial.C (d : ℚ) * f := by
  let V := IsLocalization.integerNormalization (nonZeroDivisors ℤ) f
  obtain ⟨d, hd, heq⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors ℤ) f
  refine ⟨d, V, nonZeroDivisors.ne_zero hd, ?_, ?_⟩
  · exact IsFractionRing.integerNormalization_eq_zero_iff.not.mpr hf
  · simpa only [zsmul_eq_mul, map_intCast] using heq

section Scheduled

variable (U : ℕ → NonzeroIntPolynomial) (hU : Function.Surjective U)
  (stage : PrimeIndex → ℕ) (hstage : ∀ n, {p | stage p ≤ n}.Finite)
  (β : (p : PrimeIndex) → ℤ_[p.val])
  (havoid : ∀ p j, j < stage p →
    (U j).val.eval₂ (Int.castRingHom (ZMod p.val)) (PadicInt.toZMod (β p)) ≠ 0)

include hU hstage havoid

theorem eventually_intPolynomial_norm_one (V : ℤ[X]) (hV : V ≠ 0) :
    ∀ᶠ p : PrimeIndex in Filter.cofinite,
      ‖V.eval₂ (Int.castRingHom ℚ_[p.val]) (β p : ℚ_[p.val])‖ = 1 := by
  have hu := Filter.eventually_cofinite.mpr
    (intPolynomial_nonunit_finite U hU stage hstage β havoid V hV)
  filter_upwards [hu] with p hp
  rw [← coe_intPolynomial_eval]
  exact PadicInt.isUnit_iff.mp hp

theorem eventually_ratPolynomial_norm_one (f : ℚ[X]) (hf : f ≠ 0) :
    ∀ᶠ p : PrimeIndex in Filter.cofinite,
      ‖f.eval₂ (algebraMap ℚ ℚ_[p.val]) (β p : ℚ_[p.val])‖ = 1 := by
  obtain ⟨d, V, hd, hV, hmul⟩ := exists_integer_multiple f hf
  have hVn := eventually_intPolynomial_norm_one U hU stage hstage β havoid V hV
  have hdn := eventually_intPolynomial_norm_one U hU stage hstage β havoid
    (Polynomial.C d) (by simpa using hd)
  filter_upwards [hVn, hdn] with p hpV hpd
  simp only [eval₂_C] at hpd
  change ‖(d : ℚ_[p.val])‖ = 1 at hpd
  have heval := congrArg (Polynomial.eval₂ (algebraMap ℚ ℚ_[p.val])
    (β p : ℚ_[p.val])) hmul
  have hc : (algebraMap ℚ ℚ_[p.val]).comp (algebraMap ℤ ℚ) =
      Int.castRingHom ℚ_[p.val] := Subsingleton.elim _ _
  rw [eval₂_map, eval₂_mul, eval₂_C, hc] at heval
  simp only [map_intCast] at heval
  have hn := congrArg norm heval
  rw [norm_mul, hpd, one_mul, hpV] at hn
  exact hn.symm

omit hU hstage havoid in
/-- The actual embedding of rational functions at each guard argument. -/
noncomputable def guardEvaluation
    (htrans : (p : PrimeIndex) → Transcendental ℚ (β p).val) (p : PrimeIndex) :
    RatFunc ℚ →+* ℚ_[p.val] :=
  @EvaluationDVR.evaluationHom p.val (primeFact p) (β p : ℚ_[p.val]) (htrans p)


/-- Numerator and denominator are eventually units at the actual evaluation. -/
theorem eventually_ratFunc_norm_one
    (htrans : (p : PrimeIndex) → Transcendental ℚ (β p).val)
    (f : RatFunc ℚ) (hf : f ≠ 0) :
    ∀ᶠ p : PrimeIndex in Filter.cofinite,
      ‖guardEvaluation β htrans p f‖ = 1 := by
  have hn := eventually_ratPolynomial_norm_one U hU stage hstage β havoid
    f.num (RatFunc.num_ne_zero hf)
  have hd := eventually_ratPolynomial_norm_one U hU stage hstage β havoid
    f.denom (RatFunc.denom_ne_zero f)
  filter_upwards [hn, hd] with p hpn hpd
  have heval : guardEvaluation β htrans p f =
      aeval (β p : ℚ_[p.val]) f.num / aeval (β p : ℚ_[p.val]) f.denom :=
    LocalEvaluation.evalAt_apply _ _ _
  rw [heval, norm_div]
  change ‖f.num.eval₂ (algebraMap ℚ ℚ_[p.val]) (β p : ℚ_[p.val])‖ /
    ‖f.denom.eval₂ (algebraMap ℚ ℚ_[p.val]) (β p : ℚ_[p.val])‖ = 1
  rw [hpn, hpd, div_self one_ne_zero]

omit hU hstage havoid in
/-- A unit norm is exactly multiplicative valuation one. -/
theorem mulValuation_eq_one_of_norm_eq_one {p : ℕ} [Fact p.Prime]
    (x : ℚ_[p]) (hx : ‖x‖ = 1) : Padic.mulValuation x = 1 := by
  apply le_antisymm
  · apply le_of_not_gt
    intro h
    have hn := (Padic.norm_lt_norm_iff_mulValuation_lt (x := 1) (y := x)).mpr
      (by simpa only [map_one] using h)
    simp only [norm_one, hx, lt_self_iff_false] at hn
  · apply le_of_not_gt
    intro h
    have hn := (Padic.norm_lt_norm_iff_mulValuation_lt (x := x) (y := 1)).mpr
      (by simpa only [map_one] using h)
    simp only [norm_one, hx, lt_self_iff_false] at hn

theorem eventually_ratFunc_valuation_one
    (htrans : (p : PrimeIndex) → Transcendental ℚ (β p).val)
    (f : RatFunc ℚ) (hf : f ≠ 0) :
    ∀ᶠ p : PrimeIndex in Filter.cofinite,
      EvaluationDVR.valuation p.val (guardEvaluation β htrans p) f = 1 := by
  filter_upwards [eventually_ratFunc_norm_one U hU stage hstage β havoid htrans f hf]
    with p hp
  exact mulValuation_eq_one_of_norm_eq_one (guardEvaluation β htrans p f) hp

/-- Every nonzero rational function has finite nontrivial guard valuation support. -/
theorem ratFunc_guardSupport_finite
    (htrans : (p : PrimeIndex) → Transcendental ℚ (β p).val)
    (f : RatFunc ℚ) (hf : f ≠ 0) :
    {p : PrimeIndex |
      EvaluationDVR.valuation p.val (guardEvaluation β htrans p) f ≠ 1}.Finite :=
  Filter.eventually_cofinite.mp
    (eventually_ratFunc_valuation_one U hU stage hstage β havoid htrans f hf)

end Scheduled

end UnconditionalCounterexample.GuardSupport
