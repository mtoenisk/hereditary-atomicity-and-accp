import UnconditionalCounterexample.Variations.TwoChainDescent
import UnconditionalCounterexample.Variations.TwoCentreHorizontalActual
import UnconditionalCounterexample.Variations.TwoChainRealizedReturns

/-!
# The two-chain counterexample of §9.2

The two literal square chains, the obstruction to weak ACCP, and the
factorization theorems in every unital subring all concern the same
constructed subring of the rational function field.
-/

noncomputable section
namespace UnconditionalCounterexample.TwoChains

open Filter Variations

theorem hereditarilyStronglyAtomic : Factorization.IsHereditarilyStronglyAtomic domain := by
  refine hereditarilyStronglyAtomic_of_profiles orders
    (TwoCentreHorizontal.detects_divisibility primaryData) ?_ units_signs movingElement moving_profiles ?_ ?_
  · intro c x y hx hy
    exact DiscreteOrders.natOrder_mul _ (fun h => hx (Subtype.ext h)) (fun h => hy (Subtype.ext h))
      (TwoCentreHorizontal.integral primaryData x (.endpoint c))
      (TwoCentreHorizontal.integral primaryData y (.endpoint c))
  · intro m hm c N
    exact ((eventually_ge_atTop N).and (eventually_moving_return c m hm)).exists
  · intro T hT
    unfold Factorization.IsBFDomain at hT
    push Not at hT
    obtain ⟨x, hx, hunbounded⟩ := hT
    obtain ⟨⟨n, hn, hnt⟩, hall⟩ := integer_conductor_of_unbounded T x hx hunbounded
    exact ⟨n, hn, hall n hnt⟩

/-- A single joint theorem names both literal starts of the strict chains
and computes strong atomicity inside each of the ring's own subrings. -/
theorem conclusion :
    (parameter : RatFunc ℚ) = RatFunc.X ∧ IsFractionRing domain (RatFunc ℚ) ∧
    HasStrictChainAt (parameter^2) ∧ HasStrictChainAt ((1-parameter)^2) ∧
    IsCoprime (parameter^2) ((1-parameter)^2) ∧
    ¬ Factorization.IsWeakACCP domain ∧ Factorization.IsHereditarilyStronglyAtomic domain := by
  obtain ⟨h₀, h₁, hc, hw⟩ := square_chains_not_weakACCP
  exact ⟨rfl, Univariate.fractionRing requirements, h₀, h₁, hc, hw, hereditarilyStronglyAtomic⟩

end UnconditionalCounterexample.TwoChains
