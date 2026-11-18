import UnconditionalCounterexample.PaperAtoms

/-!
# Concrete valuation compatibility for word extraction

These identities connect the complete natural-valued profile of the one
constructed domain with its actual primary/guard evaluations and pole algebra.
-/

namespace UnconditionalCounterexample.PaperConstruction
open CompleteProfiles DiscreteOrders GuardSupport

/-- Actual primary evaluation equals the exponential of the negative natural profile. -/
theorem primary_value_eq_exp_profile (z : domain) (hz : z ≠ 0) (j : ℕ) :
    PairedDomain.vertical places (.inl j) (z : RatFunc ℚ) =
      WithZero.exp (-(valuationProfiles.value (.primary j) z : ℤ)) := by
  change valuations poles places (.primary j) (z : RatFunc ℚ) = _
  rw [value_eq_exp_neg_order _ (fun h => hz (Subtype.ext h)), valuationProfiles_cast _ z hz]

/-- Vanishing outside profiles give actual units at every guard. -/
theorem guard_value_eq_one_of_outside_zero (z : domain) (hz : z ≠ 0)
    (ho : ∀ i, valuationProfiles.value (.outside i) z = 0) (p : PrimeIndex) :
    @Padic.mulValuation p.val ⟨p.property⟩
      (guardEvaluation places.guard places.guard_trans p (z : RatFunc ℚ)) = 1 := by
  have hzero : order (valuations poles places (.outside (.inl p))) (z : RatFunc ℚ) = 0 := by
    rw [← valuationProfiles_cast _ z hz, ho]
    rfl
  exact (order_eq_zero_iff _ (fun h => hz (Subtype.ext h))).mp hzero

/-- The pure natural profile gives inverse membership in the actual pole algebra. -/
theorem inverse_pole_mem_of_pure (z : domain) (hz : z ≠ 0)
    (hl : valuationProfiles.value .limit z = 0)
    (ho : ∀ i, valuationProfiles.value (.outside i) z = 0) :
    (z : RatFunc ℚ)⁻¹ ∈ PoleAlgebra.generated poles := by
  have hn : ∀ q ∈ poles, q ≠ 0 := by
    intro q hq hzq
    exact raw_constant hq (by simp [hzq])
  have hli : order (valuations poles places .limit) (z : RatFunc ℚ) = 0 := by
    rw [← valuationProfiles_cast _ z hz, hl]
    rfl
  have hoi : ∀ i, order (valuations poles places (.outside i)) (z : RatFunc ℚ) = 0 := by
    intro i
    rw [← valuationProfiles_cast _ z hz, ho]
    rfl
  exact (pole_unit_of_zero_outside poles places hn z (fun h => hz (Subtype.ext h)) hli hoi).2

end UnconditionalCounterexample.PaperConstruction
