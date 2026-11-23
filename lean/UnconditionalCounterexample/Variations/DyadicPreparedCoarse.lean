import UnconditionalCounterexample.Variations.DyadicPreparedValues
import UnconditionalCounterexample.Variations.DyadicPrefixCoarse

/-! # The finite split preview is exact outside its actual table -/

noncomputable section
namespace UnconditionalCounterexample.Variations.DyadicLedger.Calibrated
open Polynomial GuardSupport Univariate FreezingCalendar DiscreteOrders DyadicDeviations WithZero
open PrincipalProfiles FieldGeneration

variable (a : Policy)

theorem centres_known {n : ℕ} (hn : 0 < n) (c : Bool) : (centre c).val ∈ ((driver a).state n).frozen := by
  apply (driver a).frozen_iff.mpr
  refine ⟨0,hn,?_⟩
  have he := dispatcher_calendar (planner a) 0
  change (centre c).val ∈ ((driver a).actualRequest ((driver a).opening 0)).freeze
  rw [← he]
  cases c
  · exact (initially_both ∅).1
  · exact (initially_both ∅).2

private theorem frozen_guard {n : ℕ} (q : Horizontal) (hf : q.val ∈ ((driver a).state n).frozen)
    (p : PrimeIndex) (hp : p ∉ (driver a).assigned n) :
    order (UnivariateExtraction.guardVal (driver a).requirements p) (horizontalUnit q).val = 0 := by
  let D := driver a
  obtain ⟨t,ht,hf'⟩ := D.frozen_iff.mp hf
  have hnew : q.val ∈ freezeList (D.state t) ((chain D.requirements).approx t) := by
    by_cases h : (D.state t).remaining = []
    · exact (dispatcher_open (planner a) (D.state t) ((chain D.requirements).approx t) (table D.requirements t) h).2.2.1 ▸ hf'
    · have he := (dispatch_interior_roles (planner a) (D.state t) ((chain D.requirements).approx t)
          (table D.requirements t) h).1
      exact False.elim (Finset.notMem_empty q.val (he ▸ hf'))
  have late : t < (chain D.requirements).guardChain.birth p := by
    by_contra! h
    exact hp (assigned_mono D.requirements ((Nat.succ_le_succ h).trans ht)
      (show p ∈ D.assigned ((chain D.requirements).guardChain.birth p+1) from (chain D.requirements).guardChain.birth_mem p))
  have hu := FrozenGuards.after_freezing D.requirements t _ (guard_cutoff a t) p late q.val
    (Finset.mem_union_left _ (Finset.mem_union_right _ hnew)) q.property.1.ne_zero
  apply (order_eq_zero_iff _ (horizontalUnit q).ne_zero).mpr
  apply GuardSupport.mulValuation_eq_one_of_norm_eq_one
  rw [← UnivariateExtraction.eval_permanent_guard]
  change ‖EvaluationDVR.evaluationHom _ _ _ (algebraMap ℚ[X] (RatFunc ℚ) q.val)‖ = 1
  rwa [RawEvaluationPromises.evaluationHom_polynomial]

/-- The exact information supplied by monotone freezing for a field element
whose finite profile is read at the given prefix. -/
structure Exterior (n : ℕ) (x : (RatFunc ℚ)ˣ) : Prop where
  guard : ∀ p ∉ (driver a).assigned n, order (UnivariateExtraction.guardVal (driver a).requirements p) x.val = 0
  primary : ∀ p ∉ (driver a).assigned n, ∀ r (hr : (driver a).permanentRole p = some r),
    order (primaryVal a p (by rw [hr]; rfl)) x.val = expected r x.val
  horizontal : ∀ f : Horiz a, f.val.val ∉ ((driver a).state n).frozen →
    order (HorizontalOrders.valuation f.val) x.val = 0

theorem Exterior.guard_norm {n : ℕ} {x : (RatFunc ℚ)ˣ} (h : Exterior a n x) (p : PrimeIndex)
    (hp : p ∉ (driver a).assigned n) :
    ‖(permanentSite (driver a).requirements p).evaluate true (Or.inl rfl) x.val‖ = 1 := by
  have he := (order_eq_zero_iff _ x.ne_zero).mp (h.guard p hp)
  change ‖LocalEvaluation.evalAt (permanentSite (driver a).requirements p).guard.val (permanentSite (driver a).requirements p).guard_trans x.val‖ = 1
  rw [UnivariateExtraction.eval_permanent_guard]
  exact ConstructionReturns.norm_eq_one_of_mulValuation_eq_one _ he

theorem task_exterior (r : ℕ) (hx : (taskAt r).element ≠ 0) :
    Exterior a ((driver a).opening (r+1)) (Units.mk0 _ hx) where
  guard p hp := by
    apply (order_eq_zero_iff _ hx).mpr
    apply GuardSupport.mulValuation_eq_one_of_norm_eq_one
    rw [← UnivariateExtraction.eval_permanent_guard]
    exact future_task_guard a r hx p hp
  primary p hp role hr := future_task_primary a r hx p hp role hr
  horizontal f hf := by
    let x := (taskAt r).element
    change -log (HorizontalOrders.valuation f.val x) = 0
    rw [HorizontalOrders.neg_log_valuation_eq_exponents f.val x hx]
    apply Finsupp.notMem_support_iff.mp
    intro hm
    rcases factor_ready a r f.val (factor_of_exponent hx hm) with ⟨j,_,he⟩ | h
    · exact f.property.1 ⟨j,he⟩
    · exact hf h

private def exteriorGroup (n : ℕ) : Subgroup (RatFunc ℚ)ˣ where
  carrier := {x | Exterior a n x}
  one_mem' := ⟨by simp,fun _ _ r _ => by cases r <;> simp [expected],by simp⟩
  mul_mem' := by
    intro x y hx hy
    refine ⟨?_,?_,?_⟩
    · intro p hp
      simp [order_mul _ x.ne_zero y.ne_zero,hx.guard p hp,hy.guard p hp]
    · intro p hp r hr
      rw [Units.val_mul,order_mul _ x.ne_zero y.ne_zero,hx.primary p hp r hr,hy.primary p hp r hr]
      cases r <;> simp [expected,order_mul _ x.ne_zero y.ne_zero]
    · intro f hf
      simp [order_mul _ x.ne_zero y.ne_zero,hx.horizontal f hf,hy.horizontal f hf]
  inv_mem' := by
    intro x hx
    refine ⟨?_,?_,?_⟩
    · intro p hp
      simp [hx.guard p hp]
    · intro p hp r hr
      rw [Units.val_inv_eq_inv_val,order_inv,hx.primary p hp r hr]
      cases r <;> simp [expected]
    · intro f hf
      simp [hx.horizontal f hf]

private theorem known_exterior {n : ℕ} (q : Horizontal) (hq : q.val ∈ ((driver a).state n).frozen) :
    Exterior a n (horizontalUnit q) where
  guard := frozen_guard a q hq
  primary p hp r hr := future_factor a n (Or.inr hq) p hp r hr
  horizontal f hf := by
    have hn : q ≠ f.val := fun h => hf (h ▸ hq)
    change -log (HorizontalOrders.valuation f.val (factor q)) = 0
    simp [HorizontalOrders.valuation_factor_of_ne _ _ hn]

private theorem prime_horizontal (q : PrimeIndex) (f : Horizontal) :
    order (HorizontalOrders.valuation f) (q.val : RatFunc ℚ) = 0 := by
  have h : (q.val : RatFunc ℚ) = RatFunc.C (q.val : ℚ) := (map_natCast _ _).symm
  rw [h,order,HorizontalOrders.valuation_constant _ _ (Nat.cast_ne_zero.mpr q.property.ne_zero),log_one,neg_zero]

private theorem prime_exterior {n : ℕ} (q : (driver a).assigned n) :
    Exterior a n (Units.mk0 (q.val.val : RatFunc ℚ) (Nat.cast_ne_zero.mpr q.val.property.ne_zero)) := by
  have hz (p : PrimeIndex) (hp : p ∉ (driver a).assigned n) (e : RatFunc ℚ →+* ℚ_[p.val]) :
      order (EvaluationDVR.valuation p.val e) (q.val.val : RatFunc ℚ) = 0 := by
    have hne : q.val.val ≠ p.val := fun h => hp (Subtype.ext h ▸ q.property)
    simp only [order,PairedResidues.valuation_prime_eq_one_of_ne q.val.val p.val e hne,log_one,neg_zero]
  refine ⟨fun p hp => hz p hp _,?_,fun f _ => prime_horizontal q.val f.val⟩
  intro p hp r hr
  change order (primaryVal a p _) (q.val.val : RatFunc ℚ) = expected r (q.val.val : RatFunc ℚ)
  rw [show order (primaryVal a p _) (q.val.val : RatFunc ℚ) = 0 from hz p hp _]
  cases r with
  | regular c k i => exact (prime_horizontal q.val (centre c)).symm
  | auxiliary => rfl

/-- For any horizontal and guard target in the finite table the canonical
coarse factor takes its predicted values on every remaining prime. -/
theorem coarse_exterior (n : ℕ) (hn : 0 < n)
    (u : Profile (PrefixProfile.Aux ((driver a).assigned n) ((driver a).state n).role)
      (PrefixProfile.Lone ((driver a).assigned n) ((driver a).state n).role) (PrefixProfile.Known ((driver a).state n).frozen)) :
    Exterior a n (PrefixProfile.coarse ((driver a).assigned n) ((driver a).state n).role
      (table (driver a).requirements n) ((driver a).state n).frozen u) := by
  let D := driver a
  let S := exteriorGroup a n
  let K := (D.state n).frozen
  change PrefixProfile.coarse (D.assigned n) (D.state n).role (table D.requirements n) K u ∈ S
  unfold PrefixProfile.coarse DyadicSplit.coarseFactor
  simp only [Bool.false_eq_true,↓reduceIte,one_mul]
  apply S.mul_mem
  · apply S.prod_mem
    intro i _
    apply S.zpow_mem
    apply known_exterior
    cases i with
    | inl c => exact centres_known a hn c
    | inr f => exact f.property.1
  · apply S.prod_mem
    exact fun p _ => S.zpow_mem (prime_exterior a p) _

end UnconditionalCounterexample.Variations.DyadicLedger.Calibrated
