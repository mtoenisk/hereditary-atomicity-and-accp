import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.Tactic.FieldSimp

/-!
# Stability of p-adic numerator and return targets

Finite-stage coefficient approximation must preserve the norm of prescribed
nonzero evaluations and make the normalized return error small. An explicit
radius around the numerator target proves both properties. Actual membership
in the p-adic integer subring translates scaled errors into weak norm bounds;
these conditions are open because nonzero-radius p-adic closed balls are open.

All statements use the actual p-adic field and integer subring. The construction
of approximating rational coefficients is a separate step.
-/

namespace UnconditionalCounterexample.PadicTargetStability

variable {p : ℕ} [Fact p.Prime]

/-- A sufficiently close approximation to a nonzero p-adic target has exactly
the same norm and remains nonzero. -/
theorem norm_eq_and_ne_zero_of_norm_sub_lt (η z : ℚ_[p]) (hη : η ≠ 0)
    (hz : ‖z - η‖ < ‖η‖) : ‖z‖ = ‖η‖ ∧ z ≠ 0 := by
  have heq := Padic.norm_eq_of_norm_sub_lt_right hz
  exact ⟨heq, norm_pos_iff.mp (heq.symm ▸ norm_pos_iff.mpr hη)⟩

/-- The explicit return-target radius preserves norm and makes the relative
return error arbitrarily small. -/
theorem refined_target_stable_of_norm_sub_lt
    (B r z : ℚ_[p]) (ε : ℝ) (hB : B ≠ 0) (hr : r ≠ 0)
    (hz : ‖z - B * r‖ < min ‖B * r‖ (ε * ‖B * r‖)) :
    z ≠ 0 ∧ ‖z / B‖ = ‖r‖ ∧ ‖r / (z / B) - 1‖ < ε := by
  have hη : B * r ≠ 0 := mul_ne_zero hB hr
  obtain ⟨hznorm, hz0⟩ := norm_eq_and_ne_zero_of_norm_sub_lt (B * r) z hη
    (hz.trans_le (min_le_left _ _))
  refine ⟨hz0, ?_, ?_⟩
  · rw [norm_div, hznorm, norm_mul]
    exact mul_div_cancel_left₀ _ (norm_ne_zero_iff.mpr hB)
  · have hid : r / (z / B) - 1 = (B * r - z) / z := by
      field_simp
    rw [hid, norm_div, norm_sub_rev, hznorm]
    exact (div_lt_iff₀ (norm_pos_iff.mpr hη)).mpr
      (hz.trans_le (min_le_right _ _))

/-- Every nonzero refined p-adic target admits a positive stable neighborhood. -/
theorem exists_refined_target_radius
    (B r : ℚ_[p]) (ε : ℝ) (hB : B ≠ 0) (hr : r ≠ 0) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ z : ℚ_[p], ‖z - B * r‖ < δ →
      z ≠ 0 ∧ ‖z / B‖ = ‖r‖ ∧ ‖r / (z / B) - 1‖ < ε := by
  have hη : 0 < ‖B * r‖ := norm_pos_iff.mpr (mul_ne_zero hB hr)
  refine ⟨min ‖B * r‖ (ε * ‖B * r‖), lt_min hη (mul_pos hε hη), ?_⟩
  intro z hz
  exact refined_target_stable_of_norm_sub_lt B r z ε hB hr hz

/-- Actual membership in the p-adic integers after division is exactly the
corresponding error-norm bound. -/
theorem div_mem_padicInt_iff (e d : ℚ_[p]) (hd : d ≠ 0) :
    e / d ∈ PadicInt.subring p ↔ ‖e‖ ≤ ‖d‖ := by
  rw [PadicInt.mem_subring_iff, norm_div, div_le_one (norm_pos_iff.mpr hd)]

theorem error_div_prime_pow_mem_padicInt_iff (z η : ℚ_[p]) (i : ℕ) :
    (z - η) / (p : ℚ_[p]) ^ i ∈ PadicInt.subring p ↔
      ‖z - η‖ ≤ ‖(p : ℚ_[p]) ^ i‖ := by
  apply div_mem_padicInt_iff
  exact pow_ne_zero i (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)

/-- Scaled integral-error conditions are open even with a weak norm bound,
because nonzero-radius closed balls in the p-adics are open. -/
theorem isOpen_scaled_error_integral (η d : ℚ_[p]) (hd : d ≠ 0) :
    IsOpen {z : ℚ_[p] | (z - η) / d ∈ PadicInt.subring p} := by
  simp_rw [div_mem_padicInt_iff _ _ hd]
  simpa only [Metric.closedBall, dist_eq_norm_sub] using
    IsUltrametricDist.isOpen_closedBall η (norm_ne_zero_iff.mpr hd)

end UnconditionalCounterexample.PadicTargetStability
