import UnconditionalCounterexample.Variations.DyadicConcreteDomain
import UnconditionalCounterexample.Variations.DyadicSignedField
import UnconditionalCounterexample.Variations.DyadicPrefixModulus

/-! # Exact forecasts outside the prepared split table -/

noncomputable section
namespace UnconditionalCounterexample.Variations.DyadicLedger.Calibrated
open Polynomial GuardSupport RecursivePrefix Univariate FreezingCalendar OpeningCalibration DiscreteOrders WithZero
open PrincipalProfiles FieldGeneration

/-- Every single later labelled birth respects the exact orders of the
rational polynomial itself, including all early primes. -/
theorem predicts_rational (policy : Policy) (f : Horizontal) (n : ℕ) (hf : f.val ∈ ((driver policy).state n).frozen)
    (p : PrimeIndex) (hp : p ∈ ((driver policy).actualRequest n).births.primes) (r : FibreRole)
    (hr : ((driver policy).actualRequest n).role p hp = some r) :
    Orders (((driver policy).actualRequest n).births.site p hp) r f.val := by
  classical
  let D := driver policy
  by_cases h : (D.state n).remaining = []
  · let A := actualRoom policy n
    let use := installed policy n h
    by_cases ha : p ∈ A.fibres.births.primes
    · obtain ⟨_,hv,hs⟩ := use.included p ha
      rw [hs]
      exact A.old_orders p ha r (hv.symm.trans hr) ⟨f.val,Finset.mem_filter.mpr ⟨hf,f.property⟩⟩
    · rw [use.unlabelled p hp ha] at hr
      cases hr
  · have hu := (dispatch_interior_roles (planner policy) (D.state n) ((chain D.requirements).approx n)
      (table D.requirements n) h).2 p hp
    have hn : (none : Option FibreRole) = some r := hu.symm.trans hr
    cases hn

variable (a : Policy)

def expected (r : FibreRole) (x : RatFunc ℚ) : ℤ :=
  match r with
  | .regular c _ _ => order (HorizontalOrders.valuation (centre c)) x
  | .auxiliary _ _ _ => 0

theorem expected_factor (r : FibreRole) (f : Horizontal) :
    expected r (factor f) = Calibration.forecastOrder (height f.val) (some r) := by
  cases r with
  | regular c k i => exact centre_order_horizontal c f
  | auxiliary => rfl

/-- Every factor of the task's numerator or denominator is already an
earlier raw, or is in the persistent finite frozen set when layout is chosen. -/
theorem factor_ready (r : ℕ) (f : Horizontal) (hf : f.val ∈ FreezingCalendar.factors (taskAt r).element) :
    let D := driver a; let n := D.opening (r+1)
    (∃ j < n, (chain D.requirements).raw j = f.val) ∨ f.val ∈ (D.state n).frozen := by
  let D := driver a
  let t := D.opening r
  let n := D.opening (r+1)
  have ht : t < n := D.opening_strict (Nat.lt_succ_self _)
  have hc : f.val ∈ candidates r ∅ := Finset.mem_union_left _ (Finset.mem_union_right _ hf)
  rcases candidate_trichotomy ((chain D.requirements).approx t) (D.state t).frozen _ hc with h | ⟨j,h⟩ | h
  · obtain ⟨j,hj,hf'⟩ := D.frozen_iff.mp h
    exact Or.inr (D.frozen_iff.mpr ⟨j,hj.trans ht,hf'⟩)
  · exact Or.inl ⟨j.val,j.isLt.trans ht,((chain D.requirements).raw_agrees t j).symm.trans h⟩
  · have he := dispatcher_calendar (planner a) r
    have hm : f.val ∈ D.openingFreeze t ∅ := by simpa [Driver.openingFreeze,t,D.opening_rounds] using h
    exact Or.inr (D.frozen_iff.mpr ⟨t,ht,he ▸ hm⟩)

private theorem order_of_norm_one {p : PrimeIndex} {z : ℚ_[p.val]} (h : ‖z‖ = 1) : z.valuation = 0 := by
  have hn := norm_ne_zero_iff.mp (show ‖z‖ ≠ 0 from h ▸ one_ne_zero)
  simpa using EvaluationChoices.valuation_eq_of_norm_eq p.val hn (one_ne_zero : (1 : ℚ_[p.val]) ≠ 0)
    (h.trans norm_one.symm)

/-- The primary of every as-yet-unassigned labelled prime has exactly its
forecast order on every prepared horizontal, with no unknown small-prime
exceptions. -/
theorem future_factor (n : ℕ) {q : Horizontal}
    (ready : (∃ j < n, (chain (driver a).requirements).raw j = q.val) ∨ q.val ∈ ((driver a).state n).frozen)
    (p : PrimeIndex) (hn : p ∉ (driver a).assigned n) (r : FibreRole) (hr : (driver a).permanentRole p = some r) :
    order (primaryVal a p (by rw [hr]; rfl)) (factor q) = expected r (factor q) := by
  let D := driver a
  obtain ⟨b,hb,hrole⟩ := (D.permanentRole_iff p r).mp hr
  have hnle : n ≤ b := by
    by_contra! lt
    exact hn (assigned_mono D.requirements lt
      ((selection D.requirements b).batch.processed_subset_assigned (D.schedule.requested_processed b hb)))
  have hpair := ((D.actualRequest b).paired p hb).mpr (by rw [hrole]; rfl)
  rw [expected_factor]
  change order (primaryVal a p _) (horizontalUnit q).val = _
  rw [primaryVal,evaluation_order]
  change (EvaluationDVR.evaluationHom _ _ _ (algebraMap ℚ[X] (RatFunc ℚ) q.val)).valuation = _
  rw [RawEvaluationPromises.evaluationHom_polynomial,(D.permanent_role p hb).1]
  rcases ready with ⟨j,hj,he⟩ | hf
  · have hraw := (D.actualRequest b).primary_before p hb hpair ⟨j,hj.trans_le hnle⟩
    rw [(chain D.requirements).raw_agrees b ⟨j,hj.trans_le hnle⟩,he] at hraw
    rw [order_of_norm_one hraw]
    cases r with
    | auxiliary => rfl
    | regular c k i =>
      have heq : q ≠ centre c := by
        intro heq
        have hnot := (HorizontalOrders.retained_range_iff _ (fun i => ⟨(chain D.requirements).raw_monic i,
          (chain D.requirements).raw_irreducible i⟩) _).mp (centre_retained a c)
        exact hnot ⟨j,he.trans (congrArg Subtype.val heq)⟩
      have hne : q.val ≠ RegularForecast.centreFactor (if c then 1 else 0) := by
        have hc : (centre c).val = RegularForecast.centreFactor (if c then 1 else 0) := by
          cases c <;> simp [centre,zeroPoint,onePoint,RegularForecast.centreFactor]
        exact fun hh => heq (Subtype.ext (hh.trans hc.symm))
      simp [Calibration.forecastOrder,height,hne]
  · obtain ⟨j,hj,hf'⟩ := D.frozen_iff.mp hf
    exact (predicts_rational a q b (D.frozen_iff.mpr ⟨j,hj.trans_le hnle,hf'⟩) p hb r hrole).1

/-- Complete coverage of the uniform guard bound for this task's numerator,
denominator, and scalar normalizations on the actual selected batch. -/
theorem guard_cutoff (t : ℕ) :
    let D := driver a; let m := D.state t; let P := (chain D.requirements).approx t
    FrozenGuards.cutoff (m.frozen ∪ freezeList m P ∪ taskGuardData m) ≤ (selection D.requirements t).batch.cutoff := by
  let D := driver a
  let P := (chain D.requirements).approx t
  have start : t = 0 → P.state = CombinedGuardStep.zeroState := by rintro rfl; rfl
  change FrozenGuards.cutoff ((D.state t).frozen ∪ freezeList (D.state t) P ∪ taskGuardData (D.state t)) ≤ (selection D.requirements t).batch.cutoff
  rw [(selection D.requirements t).batch_used start]
  exact FrozenGuards.base_covers _ _ _ _ _

theorem future_guard_poly (t : ℕ) (p : PrimeIndex) (hp : p ∉ (driver a).assigned (t+1)) (f : ℚ[X])
    (hf : f ∈ taskGuardData ((driver a).state t)) (hn : f ≠ 0) :
    ‖f.eval₂ (algebraMap ℚ ℚ_[p.val]) (permanentSite (driver a).requirements p).guard.val‖ = 1 := by
  let D := driver a
  let C := (chain D.requirements).guardChain
  have hlate : t < C.birth p := by
    by_contra! h
    exact hp (assigned_mono D.requirements (Nat.succ_le_succ h)
      (show p ∈ D.assigned (C.birth p + 1) from C.birth_mem p))
  exact FrozenGuards.after_freezing D.requirements t _ (guard_cutoff a t) p hlate f (Finset.mem_union_right _ hf) hn

private theorem outside_preparation (r : ℕ) (p : PrimeIndex)
    (hp : p ∉ (driver a).assigned ((driver a).opening (r+1))) :
    p ∉ (driver a).assigned ((driver a).opening r+1) :=
  fun hm => hp (assigned_mono _ ((driver a).opening_strict (Nat.lt_succ_self r)) hm)

private theorem prepared_guard_data (r : ℕ) (p : PrimeIndex)
    (hp : p ∉ (driver a).assigned ((driver a).opening (r+1))) (f : ℚ[X])
    (hf : let x := (taskAt r).element; f ∈ ({x.num,x.denom,Polynomial.C x.num.leadingCoeff,
      Polynomial.C x.denom.leadingCoeff} : Finset ℚ[X])) (hn : f ≠ 0) :
    ‖f.eval₂ (algebraMap ℚ ℚ_[p.val]) (permanentSite (driver a).requirements p).guard.val‖ = 1 := by
  apply future_guard_poly a ((driver a).opening r) p (outside_preparation a r p hp) f _ hn
  simpa [taskGuardData,(driver a).opening_rounds] using hf

theorem future_task_guard (r : ℕ) (hx : (taskAt r).element ≠ 0) (p : PrimeIndex)
    (hp : p ∉ (driver a).assigned ((driver a).opening (r+1))) :
    ‖(permanentSite (driver a).requirements p).evaluate true (Or.inl rfl) (taskAt r).element‖ = 1 := by
  let x := (taskAt r).element
  have hn := prepared_guard_data a r p hp x.num (by simp [x]) (RatFunc.num_ne_zero hx)
  have hd := prepared_guard_data a r p hp x.denom (by simp [x]) x.denom_ne_zero
  change ‖LocalEvaluation.evalAt _ _ x‖ = 1
  rw [LocalEvaluation.evalAt_apply,norm_div]
  simp only [Polynomial.aeval_def,Site.branch,hn,hd,div_one]

private theorem task_scalar (r : ℕ) (hx : (taskAt r).element ≠ 0) (p : PrimeIndex)
    (hp : p ∉ (driver a).assigned ((driver a).opening (r+1))) :
    let x := (taskAt r).element
    ‖((x.num.leadingCoeff / x.denom.leadingCoeff : ℚ) : ℚ_[p.val])‖ = 1 := by
  let x := (taskAt r).element
  have hn := prepared_guard_data a r p hp (Polynomial.C x.num.leadingCoeff) (by simp [x])
    (Polynomial.C_ne_zero.mpr (leadingCoeff_ne_zero.mpr (RatFunc.num_ne_zero hx)))
  have hd := prepared_guard_data a r p hp (Polynomial.C x.denom.leadingCoeff) (by simp [x])
    (Polynomial.C_ne_zero.mpr (leadingCoeff_ne_zero.mpr x.denom_ne_zero))
  simp only [eval₂_C,Algebra.algebraMap_eq_smul_one,Rat.smul_one_eq_cast] at hn hd
  change ‖((x.num.leadingCoeff / x.denom.leadingCoeff : ℚ) : ℚ_[p.val])‖ = 1
  rw [Rat.cast_div,norm_div,hn,hd,div_one]

theorem factor_of_exponent {x : RatFunc ℚ} (hx : x ≠ 0) {q : Horizontal}
    (h : q ∈ (exponents x hx).support) : q.val ∈ FreezingCalendar.factors x := by
  apply mem_factors_of_dvd q.property.1 q.property.2 hx
  by_contra! hn
  have hzero (f : ℚ[X]) (hf : f ≠ 0) (hnd : ¬q.val ∣ f) : multiplicities (PrincipalProfiles.factors f hf) q = 0 :=
    Finsupp.notMem_support_iff.mp (fun hm => hnd ((mem_factors_iff _ _ _).mp ((mem_multiplicities_support _ _).mp hm)))
  exact Finsupp.mem_support_iff.mp h (by simp [exponents,hzero _ _ hn.1,hzero _ _ hn.2])

private def matchGroup (v : Valuation (RatFunc ℚ) ℤᵐ⁰) (r : FibreRole) : Subgroup (RatFunc ℚ)ˣ where
  carrier := {u | order v u.val = expected r u.val}
  one_mem' := by cases r <;> simp [expected]
  mul_mem' := by
    intro u w hu hw
    change order v _ = _
    rcases r with ⟨c,k,i⟩ | ⟨k,i,e⟩ <;>
      simp_all [expected,Units.val_mul,order_mul _ u.ne_zero w.ne_zero]
  inv_mem' := by
    intro u hu
    change order v _ = _
    cases r <;> simp_all [expected,Units.val_inv_eq_inv_val]

/-- At every primary outside the actual opening table, the prepared function
has its centre order (regular prime), or zero order (auxiliary prime). -/
theorem future_task_primary (r : ℕ) (hx : (taskAt r).element ≠ 0) (p : PrimeIndex)
    (hp : p ∉ (driver a).assigned ((driver a).opening (r+1))) (role : FibreRole)
    (hr : (driver a).permanentRole p = some role) :
    order (primaryVal a p (by rw [hr]; rfl)) (taskAt r).element = expected role (taskAt r).element := by
  let D := driver a
  let x := (taskAt r).element
  let e := exponents x hx
  let q := x.num.leadingCoeff / x.denom.leadingCoeff
  have hq : q ≠ 0 := div_ne_zero (leadingCoeff_ne_zero.mpr (RatFunc.num_ne_zero hx))
    (leadingCoeff_ne_zero.mpr x.denom_ne_zero)
  let v := primaryVal a p (by rw [hr]; rfl)
  let S := matchGroup v role
  have hs : scalarUnit q hq ∈ S := by
    change order v (scalarUnit q hq).val = expected role (RatFunc.C q)
    have hol : order v (scalarUnit q hq).val = 0 := by
      change order (primaryVal a p _) _ = _
      rw [scalar_primary_order]
      unfold UnivariateExtraction.guardVal
      rw [evaluation_order]
      have hc : RatFunc.C q = (q : RatFunc ℚ) := map_ratCast RatFunc.C q
      simp only [scalarUnit,Units.val_mk0,hc,map_ratCast]
      exact order_of_norm_one (task_scalar a r hx p hp)
    rw [hol]
    cases role with
    | regular c k j =>
      change 0 = -log (HorizontalOrders.valuation (centre c) (RatFunc.C q))
      rw [HorizontalOrders.valuation_constant _ q hq,log_one,neg_zero]
    | auxiliary => rfl
  have hfac (f : Horizontal) (hf : f ∈ e.support) : horizontalUnit f ∈ S :=
    future_factor a _ (factor_ready a r f (factor_of_exponent hx hf)) p hp role hr
  have hprod : e.prod (fun f z => horizontalUnit f ^ z) ∈ S :=
    S.prod_mem (fun f hf => S.zpow_mem (hfac f hf) _)
  have eqn : Units.mk0 x hx = scalarUnit q hq * e.prod (fun f z => horizontalUnit f ^ z) := by
    apply Units.ext
    simp only [Units.val_mk0,Units.val_mul,Finsupp.prod,Units.coe_prod,Units.val_zpow_eq_zpow_val]
    exact signed_factorization x hx
  change Units.mk0 x hx ∈ S
  rw [eqn]
  exact S.mul_mem hs hprod

end UnconditionalCounterexample.Variations.DyadicLedger.Calibrated
