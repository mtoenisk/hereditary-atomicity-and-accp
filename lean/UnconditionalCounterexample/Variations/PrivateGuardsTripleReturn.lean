import UnconditionalCounterexample.Variations.PrivateGuardsTripleStage

/-! # The private stages satisfy the same relative returns as the public stages -/

noncomputable section
namespace UnconditionalCounterexample.Variations.PrivateGuards.Live

open MvPolynomial GuardSupport MultivariateSelection MultiDomain

variable {r n : ℕ} {p : PrimeIndex} {M : ℕ → Type*} {G : Poly r} {tests : Finset (Poly r)}
  (s : Pair p G tests) (g : ScreenedGuard r p)

private theorem norm_prime (i : Option Bool) : ‖(p.val : g.Field i)‖ = ‖(p.val : ℚ_[p.val])‖ := by
  rw [← map_natCast (algebraMap ℚ_[p.val] (g.Field i)),norm_algebraMap']

theorem tripleTests_mixedSet (h : History r M n) {N : ℕ} {f : LocalPoly r p}
    (H : tripleTests s g h N f) (i : Option Bool) :
    aeval (s.triple g i) f ∈ mixedSet h (tripleEval s g i) (tripleValuation g i) p.val none := by
  let φ := tripleEval s g i
  let B := φ (oldDenominator h)
  let x := aeval (s.triple g i) f
  let y := tripleTarget s g h i
  have hB : B ≠ 0 := fun hz => oldDenominator_ne_zero h ((s.triple_independent g i) (hz.trans (map_zero _).symm))
  have hy : ‖y‖ = 1 := tripleTarget_norm s g h i
  have close : ‖x/B-y‖ < triplePrecision n p := (H.values i).2
  change tripleValuation g i (x - B*y) < tripleValuation g i (B*y*(p.val : g.Field i)^_)
  apply (tripleValuation_compat g i _ _).2
  rw [show x-B*y = B*(x/B-y) from by field_simp, norm_mul, norm_mul, norm_mul, hy, mul_one,
    norm_pow, norm_prime]
  exact mul_lt_mul_of_pos_left close (norm_pos_iff.mpr hB)

theorem tripleTests_relative (h : History r M n) {N : ℕ} {f : LocalPoly r p}
    (H : tripleTests s g h N f) (i : Option Bool) :
    let φ := tripleEval s g i
    let u := aeval (s.triple g i) f / φ (oldDenominator h)
    tripleValuation g i u = 1 ∧
      tripleValuation g i ((tripleTarget s g h i / u - 1)/(p.val : g.Field i)^Targets.precision (Targets.generator n)) ≤ 1 := by
  let φ := tripleEval s g i
  have hB : φ (oldDenominator h) ≠ 0 := fun hz => oldDenominator_ne_zero h ((s.triple_independent g i) (hz.trans (map_zero _).symm))
  simpa only [tripleTarget,φ,Targets.order, Nat.cast_zero, neg_zero,WithZero.exp_zero] using
    mixedSet_return h φ _ _ (tripleValuation_prime g i) none hB (tripleTests_mixedSet s g h H i)

end UnconditionalCounterexample.Variations.PrivateGuards.Live
