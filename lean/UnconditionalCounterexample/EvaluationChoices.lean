import UnconditionalCounterexample.LocalEvaluation
import Mathlib.NumberTheory.Padics.RingHoms

/-!
# Transcendental arguments with prescribed p-adic values

In ℚ_[p], a sufficiently small ball about p^n provides transcendental arguments of
prescribed valuation, including valuation two. A ball about an integer prime to p
supplies a unit with the specified residue.
-/

noncomputable section

namespace UnconditionalCounterexample.EvaluationChoices

open LocalEvaluation

variable (p : ℕ) [Fact p.Prime]

/-- Nonzero p-adic numbers with the same norm have the same integer valuation. -/
theorem valuation_eq_of_norm_eq {a b : ℚ_[p]} (ha : a ≠ 0) (hb : b ≠ 0)
    (h : ‖a‖ = ‖b‖) : a.valuation = b.valuation := by
  rw [Padic.norm_eq_zpow_neg_valuation ha, Padic.norm_eq_zpow_neg_valuation hb] at h
  exact neg_injective ((zpow_right_strictMono₀
    (by exact_mod_cast (Fact.out : p.Prime).one_lt : 1 < (p : ℝ))).injective h)

/-- Every p-adic open ball contains an argument transcendental over `ℚ`. -/
theorem exists_transcendental_near (a : ℚ_[p]) (ε : ℝ) (hε : 0 < ε) :
    ∃ b : ℚ_[p], ‖b - a‖ < ε ∧ Transcendental ℚ b := by
  obtain ⟨b, hb, ht⟩ := exists_transcendental_mem_open (ℚ_[p])
    Metric.isOpen_ball (show (Metric.ball a ε).Nonempty from ⟨a, Metric.mem_ball_self hε⟩)
  exact ⟨b, by simpa only [Metric.mem_ball, dist_eq_norm] using hb, ht⟩

/-- A transcendental p-adic argument can have any prescribed integer valuation. -/
theorem exists_transcendental_valuation (n : ℤ) :
    ∃ a : ℚ_[p], Transcendental ℚ a ∧ a ≠ 0 ∧ a.valuation = n := by
  have hp : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hpn : (p : ℚ_[p]) ^ n ≠ 0 := zpow_ne_zero _ hp
  obtain ⟨a, ha, ht⟩ := exists_transcendental_near p ((p : ℚ_[p]) ^ n)
    ‖(p : ℚ_[p]) ^ n‖ (norm_pos_iff.mpr hpn)
  have hn : ‖a‖ = ‖(p : ℚ_[p]) ^ n‖ := Padic.norm_eq_of_norm_sub_lt_right ha
  have hane : a ≠ 0 := norm_ne_zero_iff.mp (hn ▸ norm_ne_zero_iff.mpr hpn)
  refine ⟨a, ht, hane, ?_⟩
  rw [valuation_eq_of_norm_eq p hane hpn hn, Padic.valuation_zpow, Padic.valuation_p, mul_one]

/-- The residue ball about an integer prime to `p` contains a transcendental unit. -/
theorem exists_transcendental_unit_near_nat (c : ℕ) (hc : ¬ p ∣ c) :
    ∃ a : ℚ_[p], Transcendental ℚ a ∧ ‖a - (c : ℚ_[p])‖ < 1 ∧
      ‖a‖ = 1 ∧ a.valuation = 0 := by
  obtain ⟨a, ha, ht⟩ := exists_transcendental_near p (c : ℚ_[p]) 1 zero_lt_one
  have hcNorm : ‖(c : ℚ_[p])‖ = 1 := Padic.norm_natCast_eq_one_iff.mpr
    ((Fact.out : p.Prime).coprime_iff_not_dvd.mpr hc)
  have haNorm : ‖a‖ = 1 := (Padic.norm_eq_of_norm_sub_lt_right (hcNorm ▸ ha)).trans hcNorm
  have hane : a ≠ 0 := norm_ne_zero_iff.mp (haNorm ▸ one_ne_zero)
  refine ⟨a, ht, ha, haNorm, ?_⟩
  have hv := valuation_eq_of_norm_eq p hane (one_ne_zero : (1 : ℚ_[p]) ≠ 0)
    (haNorm.trans (norm_one : ‖(1 : ℚ_[p])‖ = 1).symm)
  simpa using hv

/-- p-adic integers at distance less than one have the same residue. -/
theorem toZMod_eq_of_norm_sub_lt_one {a b : ℤ_[p]} (h : ‖a - b‖ < 1) :
    PadicInt.toZMod a = PadicInt.toZMod b := by
  apply sub_eq_zero.mp
  rw [← map_sub, ← RingHom.mem_ker, PadicInt.ker_toZMod,
    PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton,
    ← PadicInt.norm_lt_one_iff_dvd]
  exact h

/-- A prescribed nonzero integer residue admits a transcendental p-adic integer unit. -/
theorem exists_transcendental_unit_residue (c : ℕ) (hc : ¬ p ∣ c) :
    ∃ a : ℤ_[p], Transcendental ℚ (a : ℚ_[p]) ∧ IsUnit a ∧
      PadicInt.toZMod a = (c : ZMod p) ∧ (a : ℚ_[p]).valuation = 0 := by
  obtain ⟨a, ht, ha, hn, hv⟩ := exists_transcendental_unit_near_nat p c hc
  let b : ℤ_[p] := ⟨a, hn.le⟩
  refine ⟨b, ht, PadicInt.isUnit_iff.mpr hn, ?_, hv⟩
  have hres := toZMod_eq_of_norm_sub_lt_one p (a := b) (b := (c : ℤ_[p])) ?_
  · simpa using hres
  · simpa only [PadicInt.norm_def, PadicInt.coe_sub, PadicInt.coe_natCast] using ha

end UnconditionalCounterexample.EvaluationChoices
