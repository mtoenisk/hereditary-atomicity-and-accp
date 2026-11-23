import UnconditionalCounterexample.Variations.TwoCentreHorizontal
import UnconditionalCounterexample.Variations.TwoChainValues

/-!
# The profiles and integer conductor of the two-chain domain

The fields of the primary-data interface are realized by the actual two-colour
construction. Both escaping-word extraction and conductor descent apply to
every unital subring of this one ring.
-/

noncomputable section
namespace UnconditionalCounterexample.TwoChains

open Filter WithZero DiscreteOrders GuardSupport Variations
open Univariate PrincipalProfiles

theorem guard_eq_chain (p : PrimeIndex) (x : RatFunc ℚ) :
    guardVal p x = UnivariateExtraction.guardVal requirements p x := by
  exact congrArg Padic.mulValuation (UnivariateExtraction.eval_permanent_guard requirements p x)

def primaryData : TwoCentreHorizontal.PrimaryData requirements where
  primary := primaryVal
  mem_domain x := by
    change x ∈ domain ↔ _
    rw [domain_eq_intersection, IntersectionDomain.mem_intersection]
    constructor
    · rintro ⟨hx, hall⟩
      exact ⟨hx, fun c j => hall (.inl (c,j)), fun p => (guard_eq_chain p x) ▸ hall (.inr p)⟩
    · rintro ⟨hx, hp, hg⟩
      refine ⟨hx, ?_⟩
      rintro (⟨c,j⟩ | p)
      · exact hp c j
      · exact (guard_eq_chain p x).symm ▸ hg p
  generator_primary := primaryVal_generator
  generator_guard p i := (guard_eq_chain p _).symm.trans (guardVal_generator p i)
  stabilizes x hx c := by
    obtain ⟨N, hN⟩ := eventually_atTop.mp (eventually_primary_order c x hx)
    refine ⟨N, fun i hi => ?_⟩
    rw [value_eq_exp_neg_order (primaryVal c i) hx, hN i hi,
      ← TwoCentreHorizontal.order_eq_orderAt c x hx, ← value_eq_exp_neg_order _ hx]

abbrev orders := TwoCentreHorizontal.orders primaryData

theorem units_signs (x : domain) (hu : IsUnit x) : x = 1 ∨ x = -1 :=
  TwoCentreHorizontal.signed_units primaryData x hu

theorem integer_conductor_of_unbounded (T : Subring domain) (x : T) (hx : x ≠ 0)
    (hu : ¬ Factorization.HasBoundedFactorizations x) :
    (∃ n : ℕ, 0 < n ∧ (n : domain) * parameter ∈ T) ∧
      ∀ n : ℕ, (n : domain) * parameter ∈ T → ∀ z : domain, (n : domain) * z ∈ T :=
  TwoCentreHorizontal.integer_conductor primaryData T x hx hu

/-- The moving element has the same horizontal order as its seed at every
retained place, since all normalized generators are pole-algebra units. -/
theorem horizontal_moving (q : MonicIrreducible ℚ) (hq : HorizontalOrders.Retained (poles requirements) q)
    (c : Bool) (n : ℕ) : HorizontalOrders.valuation q (moving generators c n) =
      if q = TwoCentreHorizontal.point c then exp (-1 : ℤ) else 1 := by
  have hgen (j : ℕ) : HorizontalOrders.valuation q (generators j) = 1 :=
    AtomProfiles.generators_horizontal_valuation raw _ (fun n => ((chain requirements).raw_monic n).ne_zero) q hq j
  induction n with
  | zero => exact TwoCentreHorizontal.seed_valuation q c
  | succ n ih => rw [moving, map_div₀, map_mul, hgen, hgen, mul_one, div_one, ih]

/-- All the endpoint, primary, and supplementary orders of these actual elements. -/
theorem moving_profiles (c : Bool) : TwoChainBox.MovingProfiles orders c (movingElement c) where
  ne_zero := movingElement_ne_zero c
  endpoint n := by
    change (-WithZero.log (HorizontalOrders.valuation _ (moving generators c n))).toNat = 1
    rw [horizontal_moving _ (TwoCentreHorizontal.retained_point requirements c), ite_eq_left rfl, log_exp]
    decide
  other_endpoint n d hdc := by
    change (-WithZero.log (HorizontalOrders.valuation _ (moving generators c n))).toNat = 0
    rw [horizontal_moving _ (TwoCentreHorizontal.retained_point requirements d),
      ite_eq_right (fun h => hdc (TwoCentreHorizontal.point_injective h)), log_one]
    rfl
  primary n j := by
    change (((-WithZero.log (primaryVal c j (moving generators c n))).toNat : ℕ) : ℤ) = _
    rw [primary_moving, ite_eq_left rfl, log_exp, neg_neg, Int.toNat_of_nonneg (primaryAtomProfile_nonneg _ _)]
  other_primary n d h j := by
    change (-WithZero.log (primaryVal d j (moving generators c n))).toNat = 0
    rw [primary_moving, ite_eq_right (Ne.symm h), neg_zero, log_exp]
    rfl
  outside n i := by
    rcases i with p | q
    · change (-WithZero.log (UnivariateExtraction.guardVal requirements p (moving generators c n))).toNat = 0
      rw [← guard_eq_chain, guard_moving, log_one]
      rfl
    · change (-WithZero.log (HorizontalOrders.valuation q.val (moving generators c n))).toNat = 0
      rw [horizontal_moving _ q.property.1, ite_eq_right (q.property.2 c), log_one]
      rfl

end UnconditionalCounterexample.TwoChains
