import UnconditionalCounterexample.Variations.TwoCentreHorizontalActual

/-!
# Opposite minimizers in the two-centre divisor box

On the pair of literal chain endpoints from §9.2, a different member gives
the minimum at each centre. Apply the finite-common-divisor theorem on this
pair in the constructed ring.
-/

noncomputable section
namespace UnconditionalCounterexample.TwoChains

open Variations TwoCentreHorizontal DiscreteOrders WithZero PrincipalProfiles

private def square (c : Bool) : domain := if c then (1 - parameter)^2 else parameter^2

private theorem square_eq_factor (c : Bool) : (square c : RatFunc ℚ) = factor (point c) ^ 2 := by
  rw [factor_point]
  cases c with
  | false =>
    change (RatFunc.X : RatFunc ℚ)^2 = (RatFunc.X - RatFunc.C (Bool.toNat false : ℚ))^2
    simp
  | true =>
    change (1 - (RatFunc.X : RatFunc ℚ))^2 = (RatFunc.X - RatFunc.C (Bool.toNat true : ℚ))^2
    simp
    ring

private theorem square_ne_zero (c : Bool) : square c ≠ 0 := by
  intro h
  have he : (square c : RatFunc ℚ) = 0 := congrArg Subtype.val h
  rw [square_eq_factor] at he
  exact pow_ne_zero _ (factor_ne_zero _) he

private theorem square_order (c d : Bool) : orders.endpoint (square c) d = if c = d then 2 else 0 := by
  change (-log (HorizontalOrders.valuation (point d) (square c : RatFunc ℚ))).toNat = _
  rw [square_eq_factor, map_pow]
  by_cases h : c = d
  · subst d
    rw [HorizontalOrders.valuation_factor_self, ← exp_nsmul]
    norm_num
  · rw [HorizontalOrders.valuation_factor_of_ne _ _ (point_injective.ne h), one_pow]
    simp [h]

/-- Both entries exceed order one at one centre, with opposite minimizers at
the two centres. Their common divisors have finitely many associate classes. -/
theorem square_pair_box :
    orders.endpoint (parameter^2) false = 2 ∧ orders.endpoint (parameter^2) true = 0 ∧
    orders.endpoint ((1-parameter)^2) false = 0 ∧ orders.endpoint ((1-parameter)^2) true = 2 ∧
    (Associates.mk '' {z : domain | z ∣ (1-parameter)^2 ∧ z ∣ parameter^2}).Finite := by
  refine ⟨square_order false false, square_order false true,
    square_order true false, square_order true true, ?_⟩
  exact TwoChainBox.finite_common_divisor_classes_pair orders (square_ne_zero true) (square_ne_zero false)
    ((square_order true false).le.trans (by decide)) ((square_order false true).le.trans (by decide))

end UnconditionalCounterexample.TwoChains
