import UnconditionalCounterexample.Hierarchy.PrescribedDomain
import Mathlib.Data.Finsupp.Weight
import Mathlib.Topology.Order.Compact

/-!
# Bounding the evaluation orders in the prescribed-length rings

A nonzero rational function has bounded orders on the entire distinguished
compact fiber. The remaining nonzero guard orders are finitely supported.
A positive integer therefore dominates all its vertical orders.
-/

noncomputable section
namespace UnconditionalCounterexample.Hierarchy.Prescribed

open GuardSupport DiscreteOrders WithZero Polynomial Set

variable (m : ℕ → ℕ) (p : PrimeIndex)

private def guardOrders (f : RatFunc ℚ) : PrimeIndex →₀ ℕ :=
  Finsupp.ofSupportFinite (fun q => if q = p then 0 else natOrder (guardVal q) f) (by
    by_cases hf : f = 0
    · subst f
      simp [natOrder]
    · apply (PaperConstruction.guardSupport f hf).subset
      intro q hq
      change (if q = p then 0 else natOrder (guardVal q) f) ≠ 0 at hq
      intro hu
      change guardVal q f = 1 at hu
      have hz := (order_eq_zero_iff (guardVal q) hf).mpr hu
      simp [natOrder, hz] at hq)

/-- Sum of the natural orders at all guards other than the distinguished prime. -/
def guardMass (p : PrimeIndex) (f : RatFunc ℚ) : ℕ := (guardOrders p f).degree

theorem guardNatOrder_zero_of_guardMass_eq_zero (f : RatFunc ℚ) (h : guardMass p f = 0)
    (q : PrimeIndex) (hq : q ≠ p) : natOrder (guardVal q) f = 0 := by
  have he := Finsupp.degree_eq_zero_iff (guardOrders p f) |>.mp h
  simpa [guardOrders, hq] using DFunLike.congr_fun he q

theorem guardMass_mul (S : Set ℚ[X]) {f g : ring m p S} (hf : f ≠ 0) (hg : g ≠ 0) :
    guardMass p ((f : RatFunc ℚ) * (g : RatFunc ℚ)) =
      guardMass p (f : RatFunc ℚ) + guardMass p (g : RatFunc ℚ) := by
  have he : guardOrders p ((f : RatFunc ℚ) * (g : RatFunc ℚ)) =
      guardOrders p f + guardOrders p g := by
    ext q
    change (if q = p then 0 else natOrder (guardVal q) (_ * _)) = _ + _
    by_cases h : q = p
    · simp [guardOrders, h]
    · simp only [guardOrders, Finsupp.ofSupportFinite_coe, ite_eq_right h]
      exact natOrder_mul _ (fun hz => hf (Subtype.ext hz)) (fun hz => hg (Subtype.ext hz))
        (((mem_ring_iff m p S f).mp f.property).2.2 q h) (((mem_ring_iff m p S g).mp g.property).2.2 q h)
  exact (congrArg Finsupp.degree he).trans (map_add ..)

private theorem row_norm_continuous (f : RatFunc ℚ) :
    Continuous (fun x => ‖EvaluationDVR.evaluationHom p.val (point m p x).val
      (point_transcendental m p x) f‖) := by
  have hpt : Continuous (fun x => (point m p x : ℚ_[p.val])) :=
    continuous_subtype_val.comp (point_embedding m p).continuous
  change Continuous (fun x => ‖LocalEvaluation.evalAt (point m p x).val _ f‖)
  simp only [LocalEvaluation.evalAt_apply]
  exact (((f.num.continuous_aeval.comp hpt).div (f.denom.continuous_aeval.comp hpt)
    (fun x hx => f.denom_ne_zero ((transcendental_iff.mp (point_transcendental m p x)) f.denom hx)))).norm

/-- The maximum over the entire compact fiber is attained at one actual point. -/
theorem exists_max_row_order (f : RatFunc ℚ) (hf : f ≠ 0) :
    ∃ z : RowPoint m, ∀ x, order (rowVal m p x) f ≤ order (rowVal m p z) f := by
  obtain ⟨z, _, hz⟩ := isCompact_univ.exists_isMinOn Set.univ_nonempty
    (row_norm_continuous m p f).continuousOn
  refine ⟨z, fun x => ?_⟩
  have h := hz (mem_univ x)
  have hv : rowVal m p z f ≤ rowVal m p x f := by
    by_contra! hv
    exact (not_lt_of_ge h) (Padic.norm_lt_norm_iff_mulValuation_lt.mpr hv)
  rw [value_eq_exp_neg_order _ hf, value_eq_exp_neg_order _ hf, exp_le_exp] at hv
  omega

private theorem exists_nat_orders (s : Finset PrimeIndex) (w : PrimeIndex → ℕ) :
    ∃ N : ℕ, 0 < N ∧ ∀ (q : PrimeIndex) (e : RatFunc ℚ →+* ℚ_[q.val]),
      order (EvaluationDVR.valuation q.val e) (N : RatFunc ℚ) = if q ∈ s then (w q : ℤ) else 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, by decide, by simp⟩
  | @insert t s ht ih =>
    obtain ⟨N, hN, hval⟩ := ih
    refine ⟨t.val ^ w t * N, Nat.mul_pos (pow_pos t.property.pos _) hN, ?_⟩
    intro q e
    have ht0 : (t.val : RatFunc ℚ) ≠ 0 := Nat.cast_ne_zero.mpr t.property.ne_zero
    have hn0 : (N : RatFunc ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
    rw [Nat.cast_mul, Nat.cast_pow, order_mul _ (pow_ne_zero _ ht0) hn0, hval,
      ← zpow_natCast, order_zpow]
    by_cases h : q = t
    · subst q; simp [order, ht]
    · simp [order, PairedSpectrum.valuation_other_prime q t e h, h]

/-- A positive integer has at least the order of f at every distinguished
point and every other guard. This applies also to functions with poles. -/
theorem exists_integer_dominating (f : RatFunc ℚ) (hf : f ≠ 0) :
    ∃ N : ℕ, 0 < N ∧ (∀ x, order (rowVal m p x) f ≤ order (rowVal m p x) (N : RatFunc ℚ)) ∧
      ∀ q : PrimeIndex, q ≠ p → order (guardVal q) f ≤ order (guardVal q) (N : RatFunc ℚ) := by
  classical
  obtain ⟨z, hz⟩ := exists_max_row_order m p f hf
  let t := (PaperConstruction.guardSupport f hf).toFinset
  let w := fun q => if q = p then natOrder (rowVal m p z) f else natOrder (guardVal q) f
  obtain ⟨N, hN, h⟩ := exists_nat_orders (insert p t) w
  refine ⟨N,hN,?_,?_⟩
  · intro x
    have he := h p (EvaluationDVR.evaluationHom _ _ (point_transcendental m p x))
    change order (rowVal m p x) (N : RatFunc ℚ) = _ at he
    rw [he]
    simp only [Finset.mem_insert_self, ite_true, w, natOrder]
    have := hz x
    omega
  · intro q hq
    have he := h q (guardEvaluation PaperConstruction.places.guard PaperConstruction.places.guard_trans q)
    change order (guardVal q) (N : RatFunc ℚ) = _ at he
    rw [he]
    by_cases hqt : q ∈ t
    · simp [w, hq, hqt, natOrder]
    · have hu : guardVal q f = 1 := by
        by_contra hval
        exact hqt ((Set.Finite.mem_toFinset _).mpr hval)
      simp [hq,hqt,(order_eq_zero_iff _ hf).mpr hu]

end UnconditionalCounterexample.Hierarchy.Prescribed
