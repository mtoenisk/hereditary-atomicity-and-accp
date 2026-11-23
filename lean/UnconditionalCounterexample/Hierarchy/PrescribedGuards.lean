import UnconditionalCounterexample.PaperConstruction
import UnconditionalCounterexample.PairedSpectrum
import UnconditionalCounterexample.DiscreteOrders

/-! # Rational normalization of the guards away from the distinguished prime -/

noncomputable section
namespace UnconditionalCounterexample.Hierarchy.Prescribed

open GuardSupport DiscreteOrders

abbrev guardVal (p : PrimeIndex) := PairedDomain.vertical PaperConstruction.places (.inr p)

/-- Prescribe the orders of a rational scalar at finitely many rational primes.
The same scalar works at every evaluation over a given prime. -/
theorem exists_scalar_orders (s : Finset PrimeIndex) (w : PrimeIndex → ℤ) :
    ∃ c : ℚ, c ≠ 0 ∧ ∀ (p : PrimeIndex) (e : RatFunc ℚ →+* ℚ_[p.val]),
      order (EvaluationDVR.valuation p.val e) (RatFunc.C c) = if p ∈ s then w p else 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, one_ne_zero, by simp⟩
  | @insert q s hq ih =>
    obtain ⟨c, hc, hw⟩ := ih
    have hq0 : (q.val : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr q.property.ne_zero
    refine ⟨(q.val : ℚ) ^ w q * c, mul_ne_zero (zpow_ne_zero _ hq0) hc, ?_⟩
    intro p e
    have hn : (q.val : RatFunc ℚ) ≠ 0 := Nat.cast_ne_zero.mpr q.property.ne_zero
    rw [map_mul, map_zpow₀, map_natCast, order_mul _ (zpow_ne_zero _ hn)
      ((_root_.map_ne_zero RatFunc.C).mpr hc), order_zpow, hw]
    by_cases h : p = q
    · subst p
      simp [order, hq]
    · simp [order, PairedSpectrum.valuation_other_prime p q e h, h]

/-- A rational rescaling of any nonzero function clears all other guard
orders and leaves the order at every evaluation over the distinguished prime unchanged. -/
theorem exists_guard_normalization (p : PrimeIndex) (f : RatFunc ℚ) (hf : f ≠ 0) :
    ∃ c : ℚ, c ≠ 0 ∧
      (∀ e : RatFunc ℚ →+* ℚ_[p.val], order (EvaluationDVR.valuation p.val e) (RatFunc.C c) = 0) ∧
      ∀ q : PrimeIndex, q ≠ p → order (guardVal q) (RatFunc.C c * f) = 0 := by
  classical
  let t := (PaperConstruction.guardSupport f hf).toFinset
  have ht (q : PrimeIndex) : q ∈ t ↔ guardVal q f ≠ 1 := Set.Finite.mem_toFinset _
  obtain ⟨c, hc, hw⟩ := exists_scalar_orders (t.erase p) fun q => -order (guardVal q) f
  refine ⟨c, hc, fun e => by simpa using hw p e, ?_⟩
  intro q hq
  rw [order_mul _ ((_root_.map_ne_zero RatFunc.C).mpr hc) hf]
  have he := hw q (guardEvaluation PaperConstruction.places.guard PaperConstruction.places.guard_trans q)
  change order (guardVal q) (RatFunc.C c) = _ at he
  rw [he]
  by_cases h : q ∈ t
  · simp [hq, h]
  · have h0 := (order_eq_zero_iff (guardVal q) hf).mpr (not_ne_iff.mp (fun hn => h ((ht q).mpr hn)))
    simp [h, h0]

end UnconditionalCounterexample.Hierarchy.Prescribed
