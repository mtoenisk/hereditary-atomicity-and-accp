import UnconditionalCounterexample.Hierarchy.CompactApproximation
import UnconditionalCounterexample.Hierarchy.EvaluationRing

/-! # A polynomial cutoff for divisibility at one point of a compact fibre -/

noncomputable section
namespace UnconditionalCounterexample.Hierarchy

open GuardSupport Polynomial Metric

/-- A single polynomial makes both products integral on the whole fibre and
makes the selected denominator a unit at the chosen point. -/
theorem exists_pair_cutoff (E : EvaluationFibers) (p : PrimeIndex) (hc : IsCompact (E p))
    (a : E p) (f g : evaluationPolynomials E) (hg : integralEvaluation E p a g ≠ 0)
    (hfg : ‖integralEvaluation E p a f‖ ≤ ‖integralEvaluation E p a g‖) :
    ∃ H : ℚ[X], (∀ b : E p,
      ‖H.eval₂ (Rat.castHom _) (b.val : ℚ_[p.val]) * (integralEvaluation E p b f : ℚ_[p.val])‖ ≤ 1 ∧
      ‖H.eval₂ (Rat.castHom _) (b.val : ℚ_[p.val]) * (integralEvaluation E p b g : ℚ_[p.val])‖ ≤ 1) ∧
      ‖H.eval₂ (Rat.castHom _) (a.val : ℚ_[p.val]) * (integralEvaluation E p a g : ℚ_[p.val])‖ = 1 := by
  classical
  let ev (h : evaluationPolynomials E) (b : E p) : ℚ_[p.val] := integralEvaluation E p b h
  have ce (h : evaluationPolynomials E) : Continuous (ev h) :=
    (h.val.continuous_eval₂ (Rat.castHom _)).comp (continuous_subtype_val.comp continuous_subtype_val)
  let t := ev g a
  have ht : t ≠ 0 := PadicInt.coe_ne_zero.mpr hg
  have hnorm : 0 < ‖t‖ := norm_pos_iff.mpr ht
  have ht1 : ‖t‖ ≤ 1 := (integralEvaluation E p a g).property
  let ball := closedBall (0 : ℚ_[p.val]) ‖t‖
  have hball : IsClopen ball := IsUltrametricDist.isClopen_closedBall _ hnorm.ne'
  let U := (ev f ⁻¹' ball) ∩ (ev g ⁻¹' ball)
  have hU : IsClopen U := (hball.preimage (ce f)).inter (hball.preimage (ce g))
  have memU (b : E p) : b ∈ U ↔ ‖ev f b‖ ≤ ‖t‖ ∧ ‖ev g b‖ ≤ ‖t‖ := by
    simp [U,ball,Metric.mem_closedBall]
  have ha : a ∈ U := (memU a).mpr ⟨hfg,le_rfl⟩
  let target := (LocallyConstant.const (E p) t⁻¹).indicator hU
  obtain ⟨H,hH⟩ := exists_polynomial_approx p (E p) hc target (ε := 1) zero_lt_one
  let h (b : E p) := H.eval₂ (Rat.castHom ℚ_[p.val]) (b.val : ℚ_[p.val])
  have inside (b : E p) (hb : b ∈ U) : ‖h b‖ = ‖t‖⁻¹ := by
    have e : target b = t⁻¹ := LocallyConstant.indicator_of_mem _ _ hb
    have happrox : ‖h b - t⁻¹‖ < 1 := e ▸ hH b
    rw [← norm_inv]
    exact Padic.norm_eq_of_norm_sub_lt_right (happrox.trans_le (by rw [norm_inv]; exact (one_le_inv₀ hnorm).mpr ht1))
  refine ⟨H,fun b => ?_,?_⟩
  · change ‖h b * ev f b‖ ≤ 1 ∧ ‖h b * ev g b‖ ≤ 1
    rw [norm_mul,norm_mul]
    by_cases hb : b ∈ U
    · rw [inside b hb]
      exact ⟨(inv_mul_le_one₀ hnorm).mpr ((memU b).mp hb).1,
        (inv_mul_le_one₀ hnorm).mpr ((memU b).mp hb).2⟩
    · have e : target b = 0 := LocallyConstant.indicator_of_notMem _ _ hb
      have hsmall : ‖h b‖ ≤ 1 := by simpa only [e,sub_zero] using (hH b).le
      have bound (u : evaluationPolynomials E) : ‖h b‖ * ‖ev u b‖ ≤ 1 := by
        calc
          _ ≤ 1 * ‖ev u b‖ := mul_le_mul_of_nonneg_right hsmall (norm_nonneg _)
          _ = ‖ev u b‖ := one_mul _
          _ ≤ 1 := (integralEvaluation E p b u).property
      exact ⟨bound f,bound g⟩
  · change ‖h a * t‖ = 1
    rw [norm_mul,inside a ha,inv_mul_cancel₀ hnorm.ne']

end UnconditionalCounterexample.Hierarchy
