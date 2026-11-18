import UnconditionalCounterexample.LocalInterpolation

/-!
# One-argument local targets

For an unpaired guard in manuscript section 8.2, use the actual linear factor
L=X-beta. The fixed remainder has constant zero and prescribed value eta at
beta. The varying constant c gives a monic target of degree d>1 and every
positive-power word derivative has a nonzero affine slope at this same beta.
-/

namespace UnconditionalCounterexample.SingleLocalInterpolation

open Polynomial LocalInterpolation

variable {K : Type*}

section Algebra
variable [Field K]

noncomputable def normalizedVanishing (β : K) : K[X] := 1 - C β⁻¹ * X

noncomputable def fixedRemainder (β η : K) (d : ℕ) : K[X] :=
  X ^ d + C ((η - β ^ d) / β) * X

noncomputable def localTarget (β η : K) (d : ℕ) (c : K) : K[X] :=
  C c * normalizedVanishing β + fixedRemainder β η d

@[simp] theorem normalizedVanishing_eval_zero (β : K) :
    (normalizedVanishing β).eval 0 = 1 := by simp [normalizedVanishing]

theorem normalizedVanishing_eval (β : K) (hβ : β ≠ 0) :
    (normalizedVanishing β).eval β = 0 := by simp [normalizedVanishing, hβ]

@[simp] theorem normalizedVanishing_derivative (β x : K) :
    (normalizedVanishing β).derivative.eval x = -β⁻¹ := by
  simp [normalizedVanishing, derivative_sub, derivative_mul]

theorem normalizedVanishing_derivative_ne_zero (β x : K) (hβ : β ≠ 0) :
    (normalizedVanishing β).derivative.eval x ≠ 0 := by simp [hβ]

theorem normalizedVanishing_natDegree_le (β : K) :
    (normalizedVanishing β).natDegree ≤ 1 := by
  unfold normalizedVanishing
  apply (natDegree_sub_le _ _).trans
  apply max_le (by simp)
  exact natDegree_mul_le.trans (by simp)

theorem fixedRemainder_eval_zero (β η : K) (d : ℕ) (hd : d ≠ 0) :
    (fixedRemainder β η d).eval 0 = 0 := by simp [fixedRemainder, hd]

theorem fixedRemainder_eval (β η : K) (d : ℕ) (hβ : β ≠ 0) :
    (fixedRemainder β η d).eval β = η := by
  simp only [fixedRemainder, eval_add, eval_pow, eval_X, eval_mul, eval_C]
  rw [div_mul_cancel₀ _ hβ]
  ring

theorem localTarget_eval_zero (β η : K) (d : ℕ) (c : K) (hd : d ≠ 0) :
    (localTarget β η d c).eval 0 = c := by
  simp [localTarget, fixedRemainder_eval_zero β η d hd]

theorem localTarget_eval (β η : K) (d : ℕ) (c : K) (hβ : β ≠ 0) :
    (localTarget β η d c).eval β = η := by
  simp [localTarget, normalizedVanishing_eval β hβ, fixedRemainder_eval β η d hβ]

theorem localTarget_monic_degree (β η : K) (d : ℕ) (c : K) (hd : 1 < d) :
    (localTarget β η d c).IsMonicOfDegree d := by
  have heq : localTarget β η d c = X ^ d +
      (C ((η - β ^ d) / β) * X + C c * normalizedVanishing β) := by
    simp only [localTarget, fixedRemainder]
    ring
  rw [heq]
  apply (isMonicOfDegree_X_pow K d).add_right
  apply lt_of_le_of_lt (natDegree_add_le_of_degree_le (n := 1) ?_ ?_) hd
  · exact natDegree_mul_le.trans (by simp)
  · exact natDegree_mul_le.trans (by simpa using normalizedVanishing_natDegree_le β)

noncomputable def wordSlope (β η : K) (H : K[X]) (a : ℕ) : K :=
  (a : K) * η ^ (a - 1) * (-β⁻¹) / H.eval β

theorem localTarget_word_derivative (β η : K) (d : ℕ) (c : K)
    (H : K[X]) (a : ℕ) (hβ : β ≠ 0) (hH : H.eval β ≠ 0) :
    wordDerivative (localTarget β η d c) H a β =
      wordSlope β η H a * c + wordDerivative (fixedRemainder β η d) H a β := by
  simpa only [localTarget, fixedRemainder_eval β η d hβ,
    normalizedVanishing_derivative, wordSlope] using
    wordDerivative_affine (normalizedVanishing β) (fixedRemainder β η d) H a β c
      (normalizedVanishing_eval β hβ) hH

theorem wordSlope_ne_zero [CharZero K] (β η : K) (H : K[X]) (a : ℕ)
    (ha : a ≠ 0) (hβ : β ≠ 0) (hη : η ≠ 0) (hH : H.eval β ≠ 0) :
    wordSlope β η H a ≠ 0 :=
  div_ne_zero (mul_ne_zero (mul_ne_zero (Nat.cast_ne_zero.mpr ha) (pow_ne_zero _ hη))
    (neg_ne_zero.mpr (inv_ne_zero hβ))) hH

theorem normalized_target_error (β η : K) (d : ℕ) (c r : K)
    (Q : K[X]) (hc : c ≠ 0) :
    C (r / c) * (localTarget β η d c).comp Q - C r * (normalizedVanishing β).comp Q =
      C c⁻¹ * (C r * (fixedRemainder β η d).comp Q) := by
  simp only [localTarget, add_comp, mul_comp, C_comp]
  rw [mul_add]
  have hc' : C (r / c) * C c = C r := by rw [← map_mul, div_mul_cancel₀ _ hc]
  have hr : C (r / c) = C c⁻¹ * C r := by rw [← map_mul, div_eq_mul_inv, mul_comm]
  rw [← mul_assoc, hc', hr]
  ring

end Algebra

section Normed
variable [NormedField K]

theorem exists_bound_word_derivatives [CharZero K] {ι : Type*}
    (t : Finset ι) (β η : K) (d : ℕ) (hβ : β ≠ 0) (hη : η ≠ 0)
    (H : ι → K[X]) (a : ι → ℕ) (r : ι → ℝ)
    (ha : ∀ i ∈ t, a i ≠ 0) (hH : ∀ i ∈ t, (H i).eval β ≠ 0) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ c : K, B < ‖c‖ → ∀ i ∈ t,
      r i < ‖wordDerivative (localTarget β η d c) (H i) (a i) β‖ := by
  obtain ⟨B, hB, hlarge⟩ := AffineNormEscape.exists_bound_norm_affine_gt t
    (fun i => wordSlope β η (H i) (a i))
    (fun i => wordDerivative (fixedRemainder β η d) (H i) (a i) β) r
    (fun i hi => wordSlope_ne_zero β η (H i) (a i) (ha i hi) hβ hη (hH i hi))
  refine ⟨B, hB, ?_⟩
  intro c hc i hi
  rw [localTarget_word_derivative β η d c (H i) (a i) hβ (hH i hi)]
  exact hlarge c hc i hi

theorem exists_bound_normalized_coefficients {ι : Type*} (t : Finset ι)
    (β η : K) (d : ℕ) (r : ι → K) (Q : ι → K[X]) (j : ι → ℕ) (ε : ι → ℝ)
    (hε : ∀ i ∈ t, 0 < ε i) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ c : K, B < ‖c‖ → ∀ i ∈ t,
      ‖(C (r i / c) * (localTarget β η d c).comp (Q i) -
        C (r i) * (normalizedVanishing β).comp (Q i)).coeff (j i)‖ < ε i := by
  obtain ⟨B, hB, hlarge⟩ := AffineNormEscape.exists_bound_norm_inv_mul_lt t
    (fun i => (C (r i) * (fixedRemainder β η d).comp (Q i)).coeff (j i)) ε hε
  refine ⟨B, hB, ?_⟩
  intro c hc i hi
  rw [normalized_target_error β η d c (r i) (Q i) (norm_pos_iff.mp (hB.trans_lt hc)), coeff_C_mul]
  exact hlarge c hc i hi

end Normed
end UnconditionalCounterexample.SingleLocalInterpolation
