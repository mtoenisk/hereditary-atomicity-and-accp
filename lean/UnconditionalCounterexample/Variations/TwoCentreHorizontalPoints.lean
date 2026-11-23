import UnconditionalCounterexample.HorizontalOrders
import UnconditionalCounterexample.DiscreteOrders
import UnconditionalCounterexample.Variations.TwoChainSeeds

/-!
# The horizontal valuations at zero and one

Translation identifies the order of a rational function's numerator and
denominator at an endpoint with their trailing degrees in the translated variable.
The two seeds represent the two linear factors up to nonzero rational constants.
-/

noncomputable section
namespace UnconditionalCounterexample.Variations.TwoCentreHorizontal

open Polynomial PrincipalProfiles WithZero

local instance : Algebra ℚ (RatFunc ℚ) := RatFunc.instAlgebraOfPolynomial ℚ ℚ

def point (c : Bool) : MonicIrreducible ℚ :=
  ⟨X - C (c.toNat : ℚ), monic_X_sub_C _, irreducible_X_sub_C _⟩

theorem factor_point (c : Bool) :
    factor (point c) = RatFunc.X - RatFunc.C (c.toNat : ℚ) := by
  simp only [PrincipalProfiles.factor, point, map_sub, RatFunc.algebraMap_X, RatFunc.algebraMap_C]

theorem point_injective : Function.Injective point := by
  intro a b h
  have he := congrArg (fun q : MonicIrreducible ℚ => q.val.coeff 0) h
  cases a <;> cases b <;> simp [point] at he ⊢

theorem polynomial_order (c : Bool) (g : ℚ[X]) (hg : g ≠ 0) :
    HorizontalOrders.valuation (point c) (algebraMap ℚ[X] (RatFunc ℚ) g) =
      exp (-((taylor (c.toNat : ℚ) g).natTrailingDegree : ℤ)) := by
  let a : RatFunc ℚ := RatFunc.X - RatFunc.C (c.toNat : ℚ)
  have hv : HorizontalOrders.valuation (point c) a = exp (-1 : ℤ) := by
    change HorizontalOrders.valuation (point c) (RatFunc.X - RatFunc.C (c.toNat : ℚ)) = _
    rw [← factor_point, HorizontalOrders.valuation_factor_self]
  have he : aeval a (taylor (c.toNat : ℚ) g) = algebraMap ℚ[X] (RatFunc ℚ) g := by
    rw [taylor_apply, aeval_comp]
    rw [map_add, aeval_X, aeval_C]
    change aeval (a + RatFunc.C (c.toNat : ℚ)) g = _
    rw [show a + RatFunc.C (c.toNat : ℚ) = RatFunc.X by simp [a], RatFunc.aeval_X_left_eq_algebraMap]
  have h := PrimaryStabilization.valuation_eval₂_eq_pow_natTrailingDegree
    (HorizontalOrders.valuation (point c)) RatFunc.C (taylor (c.toNat : ℚ) g)
    ((taylor_eq_zero _ _).not.mpr hg) a (hv ▸ exp_pos)
    (by rw [hv, exp_lt_one_iff]; decide)
    (fun _ hcoeff => HorizontalOrders.valuation_constant _ _ hcoeff)
  change HorizontalOrders.valuation (point c) (aeval a (taylor _ g)) = _ at h
  rw [he, hv, ← WithZero.exp_nsmul] at h
  simpa using h

theorem order_eq_orderAt (c : Bool) (x : RatFunc ℚ) (hx : x ≠ 0) :
    DiscreteOrders.order (HorizontalOrders.valuation (point c)) x =
      UnivariateCentres.orderAt (if c then 1 else 0) x := by
  have hv : HorizontalOrders.valuation (point c) x =
      exp (-(((taylor (c.toNat : ℚ) x.num).natTrailingDegree : ℤ) -
        (taylor (c.toNat : ℚ) x.denom).natTrailingDegree)) := by
    conv_lhs => rw [← x.num_div_denom]
    rw [map_div₀, polynomial_order c _ (RatFunc.num_ne_zero hx),
      polynomial_order c _ x.denom_ne_zero, ← exp_sub]
    congr 1
    omega
  rw [DiscreteOrders.order, hv, log_exp, neg_neg]
  cases c <;> simp [UnivariateCentres.orderAt]

theorem seed_valuation (q : MonicIrreducible ℚ) (c : Bool) :
    HorizontalOrders.valuation q (TwoChains.seed c) = if q = point c then exp (-1 : ℤ) else 1 := by
  have he : HorizontalOrders.valuation q (TwoChains.seed c) = HorizontalOrders.valuation q (factor (point c)) := by
    rw [factor_point]
    cases c with
    | false => simp [TwoChains.seed]
    | true =>
      have htwo := HorizontalOrders.valuation_constant q (2 : ℚ) (by norm_num)
      simp [TwoChains.seed, map_div₀, show HorizontalOrders.valuation q 2 = 1 by simpa using htwo]
  rw [he]
  split_ifs with h
  · subst q
    exact HorizontalOrders.valuation_factor_self _
  · exact HorizontalOrders.valuation_factor_of_ne _ _ (Ne.symm h)

end UnconditionalCounterexample.Variations.TwoCentreHorizontal
