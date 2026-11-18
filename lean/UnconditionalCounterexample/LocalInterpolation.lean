import UnconditionalCounterexample.LocalizedPolynomialJets
import UnconditionalCounterexample.AffineNormEscape
import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Local two-point targets for the simultaneous schedule

For the two retained points, interpolate with the family F_c = c L/L(0) + J,
prescribing the constant coefficient, monic degree, and values at both points. The
derivative of the word F_c^n/H is affine in c with nonzero slope in characteristic
zero.

A finite family of word derivatives therefore escapes every requested norm
bound as the norm of c increases. Simultaneously, normalized coefficients after
any fixed substitutions converge to those of L/L(0), with explicit finite
large-norm thresholds. Choosing a rational constant and approximating the local
target coefficients while meeting arithmetic/geometric restrictions are separate
construction steps.
-/

namespace UnconditionalCounterexample.LocalInterpolation

open Polynomial

variable {K : Type*}

section Algebra

variable [Field K]

/-- The two-point vanishing polynomial normalized to have constant one. -/
noncomputable def normalizedVanishing (a b : K) : K[X] :=
  C ((a * b)⁻¹) * ((X - C a) * (X - C b))

@[simp] theorem normalizedVanishing_eval_left (a b : K) :
    (normalizedVanishing a b).eval a = 0 := by simp [normalizedVanishing]

@[simp] theorem normalizedVanishing_eval_right (a b : K) :
    (normalizedVanishing a b).eval b = 0 := by simp [normalizedVanishing]

theorem normalizedVanishing_eval_zero (a b : K) (ha : a ≠ 0) (hb : b ≠ 0) :
    (normalizedVanishing a b).eval 0 = 1 := by
  simp only [normalizedVanishing, eval_mul, eval_C, eval_sub, eval_X, zero_sub,
    neg_mul_neg]
  exact inv_mul_cancel₀ (mul_ne_zero ha hb)

theorem normalizedVanishing_derivative_left (a b : K) :
    (normalizedVanishing a b).derivative.eval a = (a - b) / (a * b) := by
  simp [normalizedVanishing, derivative_mul, div_eq_mul_inv, mul_comm]

theorem normalizedVanishing_derivative_right (a b : K) :
    (normalizedVanishing a b).derivative.eval b = (b - a) / (a * b) := by
  simp [normalizedVanishing, derivative_mul, div_eq_mul_inv, mul_comm]

theorem normalizedVanishing_derivative_left_ne_zero
    (a b : K) (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b) :
    (normalizedVanishing a b).derivative.eval a ≠ 0 := by
  rw [normalizedVanishing_derivative_left]
  exact div_ne_zero (sub_ne_zero.mpr hab) (mul_ne_zero ha hb)

theorem normalizedVanishing_derivative_right_ne_zero
    (a b : K) (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b) :
    (normalizedVanishing a b).derivative.eval b ≠ 0 := by
  rw [normalizedVanishing_derivative_right]
  exact div_ne_zero (sub_ne_zero.mpr hab.symm) (mul_ne_zero ha hb)

theorem normalizedVanishing_natDegree_le (a b : K) :
    (normalizedVanishing a b).natDegree ≤ 2 := by
  apply (natDegree_mul_le).trans
  simp only [natDegree_C, zero_add]
  exact natDegree_mul_le.trans (by simp only [natDegree_X_sub_C]; rfl)

/-- Linear interpolation at two distinct points. -/
noncomputable def linearInterpolant (a b u v : K) : K[X] :=
  C u + C ((v - u) / (b - a)) * (X - C a)

@[simp] theorem linearInterpolant_eval_left (a b u v : K) :
    (linearInterpolant a b u v).eval a = u := by simp [linearInterpolant]

theorem linearInterpolant_eval_right (a b u v : K) (hab : a ≠ b) :
    (linearInterpolant a b u v).eval b = v := by
  simp only [linearInterpolant, eval_add, eval_C, eval_mul, eval_sub, eval_X]
  rw [div_mul_cancel₀ _ (sub_ne_zero.mpr hab.symm)]
  ring

theorem linearInterpolant_natDegree_le (a b u v : K) :
    (linearInterpolant a b u v).natDegree ≤ 1 := by
  apply natDegree_add_le_of_degree_le (by simp) ?_
  apply natDegree_mul_le.trans
  simp only [natDegree_C, natDegree_X_sub_C]
  omega

noncomputable def valueCorrection (a b u v : K) (d : ℕ) : K[X] :=
  linearInterpolant a b (u - a ^ d) (v - b ^ d)

/-- This remainder is fixed before the constant parameter is chosen. -/
noncomputable def fixedRemainder (a b u v : K) (d : ℕ) : K[X] :=
  X ^ d + valueCorrection a b u v d -
    C ((valueCorrection a b u v d).eval 0) * normalizedVanishing a b

/-- The exact local target with free constant parameter c. -/
noncomputable def localTarget (a b u v : K) (d : ℕ) (c : K) : K[X] :=
  C c * normalizedVanishing a b + fixedRemainder a b u v d

theorem fixedRemainder_eval_zero (a b u v : K) (d : ℕ)
    (ha : a ≠ 0) (hb : b ≠ 0) (hd : d ≠ 0) :
    (fixedRemainder a b u v d).eval 0 = 0 := by
  simp [fixedRemainder, normalizedVanishing_eval_zero a b ha hb, hd]

theorem localTarget_eval_zero (a b u v : K) (d : ℕ) (c : K)
    (ha : a ≠ 0) (hb : b ≠ 0) (hd : d ≠ 0) :
    (localTarget a b u v d c).eval 0 = c := by
  simp [localTarget, normalizedVanishing_eval_zero a b ha hb,
    fixedRemainder_eval_zero a b u v d ha hb hd]

@[simp] theorem fixedRemainder_eval_left (a b u v : K) (d : ℕ) :
    (fixedRemainder a b u v d).eval a = u := by
  simp [fixedRemainder, valueCorrection]

theorem fixedRemainder_eval_right (a b u v : K) (d : ℕ) (hab : a ≠ b) :
    (fixedRemainder a b u v d).eval b = v := by
  simp [fixedRemainder, valueCorrection, linearInterpolant_eval_right a b _ _ hab]

@[simp] theorem localTarget_eval_left (a b u v : K) (d : ℕ) (c : K) :
    (localTarget a b u v d c).eval a = u := by simp [localTarget]

theorem localTarget_eval_right (a b u v : K) (d : ℕ) (c : K) (hab : a ≠ b) :
    (localTarget a b u v d c).eval b = v := by
  simp [localTarget, fixedRemainder_eval_right a b u v d hab]

theorem localTarget_monic_degree (a b u v : K) (d : ℕ) (c : K) (hd : 2 < d) :
    (localTarget a b u v d c).IsMonicOfDegree d := by
  have heq : localTarget a b u v d c = X ^ d +
      (valueCorrection a b u v d +
        C (c - (valueCorrection a b u v d).eval 0) * normalizedVanishing a b) := by
    simp only [localTarget, fixedRemainder, map_sub]
    ring
  rw [heq]
  apply (isMonicOfDegree_X_pow K d).add_right
  apply lt_of_le_of_lt (natDegree_add_le_of_degree_le (n := 2)
    ((linearInterpolant_natDegree_le a b _ _).trans (by omega)) ?_) hd
  apply natDegree_mul_le.trans
  simpa only [natDegree_C, zero_add] using normalizedVanishing_natDegree_le a b

/-- The evaluated formal derivative of the rational word F^n/H. -/
noncomputable def wordDerivative (F H : K[X]) (n : ℕ) (x : K) : K :=
  ((F ^ n).derivative.eval x * H.eval x -
    (F ^ n).eval x * H.derivative.eval x) / (H.eval x) ^ 2

/-- The polynomial quotient-rule expression agrees with the actual first jet
of the corresponding element of any localization containing the denominator. -/
theorem localized_word_derivative
    (M : Submonoid K[X]) (A : Type*) [CommRing A] [Algebra K[X] A]
    [IsLocalization M A] (x : K) (hx : ∀ m : M, (m : K[X]).eval x ≠ 0)
    (F : K[X]) (m : M) (n : ℕ) :
    (LocalizedPolynomialJets.localizedFirstJet M A x hx
      (IsLocalization.mk' A (F ^ n) m)).snd = wordDerivative F (m : K[X]) n x :=
  LocalizedPolynomialJets.localizedFirstJet_mk'_snd M A x hx (F ^ n) m

/-- Fixed values and an affine first derivative give an affine derivative for
every listed rational word, without restricting its positive exponent modulo p. -/
theorem wordDerivative_affine
    (ell J H : K[X]) (n : ℕ) (x c : K)
    (hell : ell.eval x = 0) (hH : H.eval x ≠ 0) :
    wordDerivative (C c * ell + J) H n x =
      ((n : K) * J.eval x ^ (n - 1) * ell.derivative.eval x / H.eval x) * c +
        wordDerivative J H n x := by
  simp only [wordDerivative, derivative_pow, derivative_add, derivative_mul,
    derivative_C, zero_mul, zero_add, eval_mul, eval_add, eval_C, eval_pow, hell,
    mul_zero]
  field_simp [hH]
  ring

noncomputable def wordSlope (a b v : K) (H : K[X]) (n : ℕ) (x : K) : K :=
  (n : K) * v ^ (n - 1) * (normalizedVanishing a b).derivative.eval x / H.eval x

theorem localTarget_word_derivative_left
    (a b u v : K) (d : ℕ) (c : K) (H : K[X]) (n : ℕ) (hH : H.eval a ≠ 0) :
    wordDerivative (localTarget a b u v d c) H n a =
      wordSlope a b u H n a * c + wordDerivative (fixedRemainder a b u v d) H n a := by
  simpa only [localTarget, fixedRemainder_eval_left, wordSlope] using
    wordDerivative_affine (normalizedVanishing a b) (fixedRemainder a b u v d)
      H n a c (normalizedVanishing_eval_left a b) hH

theorem localTarget_word_derivative_right
    (a b u v : K) (d : ℕ) (c : K) (H : K[X]) (n : ℕ)
    (hab : a ≠ b) (hH : H.eval b ≠ 0) :
    wordDerivative (localTarget a b u v d c) H n b =
      wordSlope a b v H n b * c + wordDerivative (fixedRemainder a b u v d) H n b := by
  simpa only [localTarget, fixedRemainder_eval_right a b u v d hab, wordSlope] using
    wordDerivative_affine (normalizedVanishing a b) (fixedRemainder a b u v d)
      H n b c (normalizedVanishing_eval_right a b) hH

/-- Characteristic zero is the needed condition on the word exponent: even
when a residue prime divides n, its image in the local field is nonzero. -/
theorem wordSlope_left_ne_zero [CharZero K]
    (a b u : K) (H : K[X]) (n : ℕ) (hn : n ≠ 0)
    (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b) (hu : u ≠ 0) (hH : H.eval a ≠ 0) :
    wordSlope a b u H n a ≠ 0 := by
  exact div_ne_zero
    (mul_ne_zero (mul_ne_zero (Nat.cast_ne_zero.mpr hn) (pow_ne_zero _ hu))
      (normalizedVanishing_derivative_left_ne_zero a b ha hb hab)) hH

theorem wordSlope_right_ne_zero [CharZero K]
    (a b v : K) (H : K[X]) (n : ℕ) (hn : n ≠ 0)
    (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b) (hv : v ≠ 0) (hH : H.eval b ≠ 0) :
    wordSlope a b v H n b ≠ 0 := by
  exact div_ne_zero
    (mul_ne_zero (mul_ne_zero (Nat.cast_ne_zero.mpr hn) (pow_ne_zero _ hv))
      (normalizedVanishing_derivative_right_ne_zero a b ha hb hab)) hH

/-- After any fixed polynomial substitution and scalar normalization, the error
from the normalized vanishing polynomial is exactly c⁻¹ times fixed data. -/
theorem normalized_target_error
    (a b u v : K) (d : ℕ) (c r : K) (Q : K[X]) (hc : c ≠ 0) :
    C (r / c) * (localTarget a b u v d c).comp Q -
        C r * (normalizedVanishing a b).comp Q =
      C (c⁻¹) * (C r * (fixedRemainder a b u v d).comp Q) := by
  simp only [localTarget, add_comp, mul_comp, C_comp]
  rw [mul_add]
  have hc' : C (r / c) * C c = C r := by
    rw [← map_mul, div_mul_cancel₀ _ hc]
  rw [← mul_assoc, hc']
  have hr : C (r / c) = C c⁻¹ * C r := by
    rw [← map_mul, div_eq_mul_inv, mul_comm]
  rw [hr]
  ring

theorem normalized_target_error_coeff
    (a b u v : K) (d : ℕ) (c r : K) (Q : K[X]) (hc : c ≠ 0) (j : ℕ) :
    (C (r / c) * (localTarget a b u v d c).comp Q -
        C r * (normalizedVanishing a b).comp Q).coeff j =
      c⁻¹ * (C r * (fixedRemainder a b u v d).comp Q).coeff j := by
  rw [normalized_target_error a b u v d c r Q hc, coeff_C_mul]

end Algebra

section Normed

variable [NormedField K]

/-- A single lower bound on the norm of c forces all finitely many word
derivatives past their requested bounds at both retained points. -/
theorem exists_bound_word_derivatives [CharZero K]
    {ι : Type*} (t : Finset ι) (a b u v : K) (d : ℕ)
    (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b) (hu : u ≠ 0) (hv : v ≠ 0)
    (H : ι → K[X]) (n : ι → ℕ) (r : ι → ℝ)
    (hn : ∀ i ∈ t, n i ≠ 0)
    (hHa : ∀ i ∈ t, (H i).eval a ≠ 0)
    (hHb : ∀ i ∈ t, (H i).eval b ≠ 0) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ c : K, B < ‖c‖ → ∀ i ∈ t,
      r i < ‖wordDerivative (localTarget a b u v d c) (H i) (n i) a‖ ∧
      r i < ‖wordDerivative (localTarget a b u v d c) (H i) (n i) b‖ := by
  obtain ⟨Ba, hBa, hlargeA⟩ := AffineNormEscape.exists_bound_norm_affine_gt t
    (fun i => wordSlope a b u (H i) (n i) a)
    (fun i => wordDerivative (fixedRemainder a b u v d) (H i) (n i) a) r
    (fun i hi => wordSlope_left_ne_zero a b u (H i) (n i) (hn i hi)
      ha hb hab hu (hHa i hi))
  obtain ⟨Bb, hBb, hlargeB⟩ := AffineNormEscape.exists_bound_norm_affine_gt t
    (fun i => wordSlope a b v (H i) (n i) b)
    (fun i => wordDerivative (fixedRemainder a b u v d) (H i) (n i) b) r
    (fun i hi => wordSlope_right_ne_zero a b v (H i) (n i) (hn i hi)
      ha hb hab hv (hHb i hi))
  refine ⟨max Ba Bb, hBa.trans (le_max_left _ _), ?_⟩
  intro c hc i hi
  constructor
  · rw [localTarget_word_derivative_left a b u v d c (H i) (n i) (hHa i hi)]
    exact hlargeA c ((le_max_left _ _).trans_lt hc) i hi
  · rw [localTarget_word_derivative_right a b u v d c (H i) (n i) hab (hHb i hi)]
    exact hlargeB c ((le_max_right _ _).trans_lt hc) i hi

/-- Finitely many coefficient congruence requirements, including different
substitutions and scalar denominator clearings, follow from one large-norm bound.
Every coefficient on the right is fixed independently of c. -/
theorem exists_bound_normalized_coefficients
    {ι : Type*} (t : Finset ι) (a b u v : K) (d : ℕ)
    (r : ι → K) (Q : ι → K[X]) (j : ι → ℕ) (ε : ι → ℝ)
    (hε : ∀ i ∈ t, 0 < ε i) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ c : K, B < ‖c‖ → ∀ i ∈ t,
      ‖(C (r i / c) * (localTarget a b u v d c).comp (Q i) -
        C (r i) * (normalizedVanishing a b).comp (Q i)).coeff (j i)‖ < ε i := by
  obtain ⟨B, hB, hlarge⟩ := AffineNormEscape.exists_bound_norm_inv_mul_lt t
    (fun i => (C (r i) * (fixedRemainder a b u v d).comp (Q i)).coeff (j i)) ε hε
  refine ⟨B, hB, ?_⟩
  intro c hc i hi
  rw [normalized_target_error_coeff a b u v d c (r i) (Q i)
    (norm_pos_iff.mp (hB.trans_lt hc)) (j i)]
  exact hlarge c hc i hi

end Normed

end UnconditionalCounterexample.LocalInterpolation
