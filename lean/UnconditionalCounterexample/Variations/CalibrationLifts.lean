import Mathlib.NumberTheory.Padics.Hensel
import Mathlib.Topology.Algebra.Polynomial
import UnconditionalCounterexample.EvaluationChoices

/-! # Exact positive valuations at a transcendental lift of a simple root -/

namespace UnconditionalCounterexample.Calibration

open Polynomial

variable (p : ℕ) [Fact p.Prime]

private theorem aeval_int {A : Type*} [CommRing A] (f : ℤ[X]) (a : ℤ) :
    aeval (a : A) f = ((f.eval a : ℤ) : A) := eval₂_at_apply (Int.castRingHom A) a

/-- Hensel lifting for the shifted target gives an integral argument in the
specified residue class at which the polynomial takes the exact value
`p ^ l`. -/
theorem exists_eval_eq_prime_pow (f : ℤ[X]) (a : ℤ) (l : ℕ) (hl : 0 < l)
    (hroot : (p : ℤ) ∣ f.eval a) (hsimple : ¬ (p : ℤ) ∣ f.derivative.eval a) :
    ∃ z : ℤ_[p], ‖z - (a : ℤ_[p])‖ < 1 ∧ aeval z f = (p : ℤ_[p]) ^ l := by
  let F : ℤ[X] := f - C ((p : ℤ)^l)
  have hder : ‖aeval (a : ℤ_[p]) F.derivative‖ = 1 := by
    simp only [F, derivative_sub, derivative_C, sub_zero, aeval_int]
    apply le_antisymm (PadicInt.norm_le_one _)
    exact le_of_not_gt (fun ht => hsimple (PadicInt.norm_intCast_lt_one_iff.mp ht))
  have hval : ‖aeval (a : ℤ_[p]) F‖ < 1 := by
    rw [aeval_int, PadicInt.norm_intCast_lt_one_iff (p := p)]
    simpa [F] using dvd_sub hroot (dvd_pow_self (p : ℤ) hl.ne')
  obtain ⟨z, hz, hdist, _, _⟩ := hensels_lemma (F := F) (a := (a : ℤ_[p]))
    (by rwa [hder, one_pow])
  refine ⟨z, hder ▸ hdist, ?_⟩
  simpa [F, sub_eq_zero] using hz

/-- At a simple root modulo `p`, one can assign any positive integer value
to the polynomial while choosing a transcendental integral argument in the
original residue class. -/
theorem exists_transcendental_lift (f : ℤ[X]) (a : ℤ) (l : ℕ) (hl : 0 < l)
    (hroot : (p : ℤ) ∣ f.eval a) (hsimple : ¬ (p : ℤ) ∣ f.derivative.eval a) :
    ∃ α : ℤ_[p], Transcendental ℚ (α : ℚ_[p]) ∧ PadicInt.toZMod α = (a : ZMod p) ∧
      aeval (α : ℚ_[p]) f ≠ 0 ∧ (aeval (α : ℚ_[p]) f).valuation = l := by
  obtain ⟨z, hza, hfz⟩ := exists_eval_eq_prime_pow p f a l hl hroot hsimple
  let target := (p : ℚ_[p]) ^ l
  have htarget : target ≠ 0 := pow_ne_zero _ (by exact_mod_cast (Fact.out : p.Prime).ne_zero)
  let U := Metric.ball (a : ℚ_[p]) 1 ∩
    (fun t : ℚ_[p] => aeval t f) ⁻¹' Metric.ball target ‖target‖
  have hopen : IsOpen U := Metric.isOpen_ball.inter (Metric.isOpen_ball.preimage f.continuous_aeval)
  have hne : U.Nonempty := by
    refine ⟨(z : ℚ_[p]), ?_, ?_⟩
    · simpa only [Metric.mem_ball, dist_eq_norm, PadicInt.norm_def, PadicInt.coe_sub,
        PadicInt.coe_intCast] using hza
    · have hv : aeval (z : ℚ_[p]) f = target := by
        change aeval ((algebraMap ℤ_[p] ℚ_[p]) z) f = _
        rw [aeval_algebraMap_apply, hfz]
        simp [target]
      change aeval (z : ℚ_[p]) f ∈ Metric.ball target ‖target‖
      rw [hv]
      exact Metric.mem_ball_self (norm_pos_iff.mpr htarget)
  obtain ⟨t, ⟨hta, hft⟩, ht⟩ := LocalEvaluation.exists_transcendental_mem_open ℚ_[p] hopen hne
  have hta' : ‖t - (a : ℚ_[p])‖ < 1 := by simpa only [Metric.mem_ball, dist_eq_norm] using hta
  have htint : ‖t‖ ≤ 1 := by
    simpa only [sub_add_cancel] using
      (Padic.nonarchimedean (t - (a : ℚ_[p])) a).trans
        (max_le hta'.le (PadicInt.norm_le_one (a : ℤ_[p])))
  let α : ℤ_[p] := ⟨t, htint⟩
  have hfn : ‖aeval t f‖ = ‖target‖ := Padic.norm_eq_of_norm_sub_lt_right
    (by simpa only [Set.mem_preimage, Metric.mem_ball, dist_eq_norm] using hft)
  have hfne : aeval t f ≠ 0 := norm_ne_zero_iff.mp (hfn ▸ norm_ne_zero_iff.mpr htarget)
  refine ⟨α, ht, ?_, hfne, ?_⟩
  · simpa using EvaluationChoices.toZMod_eq_of_norm_sub_lt_one p (a := α) (b := (a : ℤ_[p])) hta'
  · change (aeval t f).valuation = _
    rw [EvaluationChoices.valuation_eq_of_norm_eq p hfne htarget hfn]
    simp [target, Padic.valuation_pow]

end UnconditionalCounterexample.Calibration
