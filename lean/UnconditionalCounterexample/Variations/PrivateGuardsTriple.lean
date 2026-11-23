import UnconditionalCounterexample.Variations.PrivateGuardsMainStage
import UnconditionalCounterexample.Variations.DimensionGuardSites
import UnconditionalCounterexample.Variations.DimensionRecoveryStage

/-!
# The complete fibre at a private prime

A screened unramified guard and the two rational private points have three
different maximal evaluation ideals. One lower-coefficient neighbourhood
prescribes the normalized value at each point and carries all the
coefficient and word-gradient estimates for their joint vanishing ideal.
-/

noncomputable section
namespace UnconditionalCounterexample.Variations.PrivateGuards

open MvPolynomial GuardSupport MultivariateSelection Filter
open scoped Topology

variable {r : ℕ} {p : PrimeIndex} {G : Poly r} {tests : Finset (Poly r)}
  (s : Pair p G tests) (g : ScreenedGuard r p)

namespace Pair

abbrev triple := g.points s.point

private theorem point_injective : Function.Injective s.point := by
  intro i j he
  apply s.kernels_injective
  exact congrArg (fun x : Fin (r+1) → ℚ_[p.val] => RingHom.ker (aeval (R := ℚ_[p.val]) x).toRingHom) he

theorem triple_distinct : Function.Injective fun i =>
    RingHom.ker (aeval (R := ℚ_[p.val]) (s.triple g i)).toRingHom :=
  g.points_distinct s.point s.point_injective

theorem triple_independent (i : Option Bool) : AlgebraicIndependent ℚ (s.triple g i) := by
  cases i with
  | none => exact g.independent
  | some b => exact s.point_independent b

abbrev generators := recoveryGenerators (K := ℚ_[p.val]) (s.triple g)

def tripleFloor (n : ℕ) := (s.generators g).threshold (p.val : ℚ_[p.val])
  (Nat.cast_ne_zero.mpr p.property.ne_zero) Padic.norm_p_lt_one (g.points_generate s.point) (s.triple_distinct g) n

/-- The value and full recovery tests, with one exponent shared by the three branches. -/
structure TripleTests {κ : Type} (n : ℕ) (D : Poly r) (target : ∀ i : Option Bool, g.Field i)
    (ε : ℝ) (H : κ → Live.LocalPoly r p) (a : κ → ℕ)
    (N : ℕ) (f : Live.LocalPoly r p) : Prop where
  values : ∀ i, let z := aeval (s.triple g i) f / aeval (s.triple g i) D
                ‖z‖ = 1 ∧ ‖z - target i‖ < ε
  denominators : ∀ t ≤ n, ∀ w, RecoveryGenerators.denScale (p.val : ℚ_[p.val]) Padic.norm_p_lt_one t (H w) + n*n ≤
    ((s.generators g).genScale p.val Padic.norm_p_lt_one t + N) * a w
  coefficients : ∀ t ≤ n, ∀ m,
    ‖(p.val : ℚ_[p.val])^N * scaledCoefficient ((p.val : ℚ_[p.val])^t)
        ((p.val : ℚ_[p.val])^((s.generators g).genScale p.val Padic.norm_p_lt_one t)) m f -
      scaledCoefficient ((p.val : ℚ_[p.val])^t)
        ((p.val : ℚ_[p.val])^((s.generators g).genScale p.val Padic.norm_p_lt_one t)) m
        ((s.generators g).direction p.val n)‖ ≤ ‖(p.val : ℚ_[p.val])‖^(n*n)
  gradients : ∀ i w, ∃ α : g.Field i, α ≠ 0 ∧ ‖α⁻¹‖ ≤ ‖(p.val : ℚ_[p.val])‖^(n*n) ∧
    ‖α⁻¹ • residueWordGradient (s.triple g i) f (H w) (a w) -
      ∑ j : Fin (s.generators g).count,
        (algebraMap ℚ_[p.val] (g.Field i) (p.val : ℚ_[p.val]) ^ n)^j.val •
          (fun l => aeval (s.triple g i) (pderiv l ((s.generators g).gen j)))‖ ≤
      ‖(p.val : ℚ_[p.val])‖^(n*n)

/-- The three-point input to the simultaneous rational polynomial selector. -/
theorem triple_open {κ : Type} [Fintype κ] (n d : ℕ) (hd : s.tripleFloor g n ≤ d)
    (leading : Live.LocalPoly r p) (hL : leading.totalDegree ≤ d)
    (D : Poly r) (hD : D ≠ 0) (target : ∀ i : Option Bool, g.Field i)
    (ht : ∀ i, ‖target i‖ = 1) (ε : ℝ) (hε : 0 < ε)
    (H : κ → Live.LocalPoly r p) (a : κ → ℕ) (ha : ∀ w, 0 < a w)
    (hH : ∀ i w, aeval (s.triple g i) (H w) ≠ 0) :
    ∃ L : Live.OpenLower r d p, ∃ N : ℕ, ∀ q : Live.LocalPoly r p, q.totalDegree < d →
      (fun m => q.coeff m) ∈ L.neighborhood → s.TripleTests g n D target ε H a N (leading + q) := by
  let B (i : Option Bool) := aeval (s.triple g i) D
  have hB (i : Option Bool) : B i ≠ 0 := fun he =>
    hD ((s.triple_independent g i) (he.trans (map_zero _).symm))
  let S (i : Option Bool) := (fun z : g.Field i => z / B i) ⁻¹' Metric.ball (target i) (min ε 1)
  have hS (i : Option Bool) : S i ∈ 𝓝 (target i * B i) := by
    apply (Metric.isOpen_ball.preimage (continuous_id.div_const _)).mem_nhds
    change target i * B i / B i ∈ Metric.ball (target i) (min ε 1)
    rw [mul_div_cancel_right₀ _ (hB i)]
    exact Metric.mem_ball_self (lt_min hε zero_lt_one)
  obtain ⟨N,T,hT,U,hU,h⟩ := (s.generators g).exists_recovery_stage p.val
    (Nat.cast_ne_zero.mpr p.property.ne_zero) Padic.norm_p_lt_one (g.points_generate s.point)
    (s.triple_distinct g) n d hd leading hL (fun i => target i * B i)
    (fun i => mul_ne_zero (norm_ne_zero_iff.mp ((ht i).symm ▸ one_ne_zero)) (hB i))
    S hS H a ha hH
  refine ⟨⟨T,hT,U,hU⟩,N,fun q hq hqU => ?_⟩
  obtain ⟨hv,hden,hco,hgr⟩ := h q hq hqU
  refine ⟨fun i => ?_,hden,hco,hgr⟩
  let z := aeval (s.triple g i) (leading + q) / B i
  have hz : ‖z - target i‖ < min ε 1 := by
    simpa only [S,Set.mem_preimage,Metric.mem_ball,dist_eq_norm] using hv i
  have hlt : ‖z + -(target i)‖ < max ‖z‖ ‖-(target i)‖ := by
    rw [← sub_eq_add_neg,norm_neg,ht]
    exact (hz.trans_le (min_le_right ..)).trans_le (le_max_right ..)
  refine ⟨?_,hz.trans_le (min_le_left ..)⟩
  simpa only [norm_neg,ht] using IsUltrametricDist.norm_eq_of_add_norm_lt_max hlt

end Pair
end UnconditionalCounterexample.Variations.PrivateGuards
