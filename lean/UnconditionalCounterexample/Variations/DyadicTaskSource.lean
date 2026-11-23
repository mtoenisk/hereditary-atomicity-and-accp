import UnconditionalCounterexample.Variations.DyadicSignedMass
import UnconditionalCounterexample.Variations.DyadicPreparedCoarse
import UnconditionalCounterexample.Variations.DyadicPrefixInstruction

/-! # Reading the prepared task on its actual finite list of primes -/

noncomputable section
namespace UnconditionalCounterexample.Variations.DyadicLedger.Calibrated
open Polynomial GuardSupport Univariate FreezingCalendar OpeningCalibration Calibration
open DiscreteOrders DyadicDeviations

variable (a : Policy)

def permanentBranch (x : (RatFunc ℚ)ˣ) (b : Bool) (p : PrimeIndex) : ℤ :=
  (DyadicSplit.branchValue (permanentSite (driver a).requirements p) b x.val).valuation

theorem primary_permanentBranch (x : (RatFunc ℚ)ˣ) (p : PrimeIndex)
    (h : ((driver a).permanentRole p).isSome) :
    order (primaryVal a p h) x.val = permanentBranch a x false p := by
  have hb : MixedStageSelection.Active (permanentSite (driver a).requirements p).paired false :=
    Or.inr (((driver a).paired_iff_role p).mpr h)
  rw [primaryVal, evaluation_order, permanentBranch, DyadicSplit.branchValue, dite_eq_left hb]

theorem guard_permanentBranch (x : (RatFunc ℚ)ˣ) (p : PrimeIndex) :
    order (UnivariateExtraction.guardVal (driver a).requirements p) x.val = permanentBranch a x true p := by
  have hb : MixedStageSelection.Active (permanentSite (driver a).requirements p).paired true := Or.inl rfl
  rw [UnivariateExtraction.guardVal, evaluation_order, permanentBranch, DyadicSplit.branchValue, dite_eq_left hb,
    ← UnivariateExtraction.eval_permanent_guard]
  rfl

theorem branchOrder_at (n : ℕ) (x : (RatFunc ℚ)ˣ) (b : Bool) (p : PrimeIndex)
    (hp : p ∈ (driver a).assigned n) :
    PrefixProfile.branchOrder ((driver a).assigned n) (table (driver a).requirements n) x.val b p =
      permanentBranch a x b p := by
  rw [PrefixProfile.branchOrder,dite_eq_left hp,table_eq_permanentSite]
  rfl

private theorem actual_reads (x : (RatFunc ℚ)ˣ) :
    MassReindex.Reads (massIndexing a) (signed a x) (permanentBranch a x false) (permanentBranch a x true) where
  regular_primary c k i := by
    cases c with
    | false => exact ((signed_values a x (.plus k i)).trans (primary_permanentBranch a x _ (by rw [regularPrime_role]; rfl))).symm
    | true => exact ((signed_values a x (.minus k i)).trans (primary_permanentBranch a x _ (by rw [regularPrime_role]; rfl))).symm
  regular_guard c k i := by
    cases c with
    | false => exact ((signed_values a x (.other (.plusGuard k i))).trans (guard_permanentBranch a x _)).symm
    | true => exact ((signed_values a x (.other (.minusGuard k i))).trans (guard_permanentBranch a x _)).symm
  aux_primary k j := ((signed_values a x (.other (.auxiliary k j))).trans
    (primary_permanentBranch a x j.prime (by rw [j.role_eq]; rfl))).symm
  aux_guard k j := ((signed_values a x (.other (.auxiliaryGuard k j))).trans (guard_permanentBranch a x _)).symm

abbrev prefixSigned (n : ℕ) (x : (RatFunc ℚ)ˣ) :=
  PrefixProfile.signed ((driver a).assigned n) ((driver a).state n).role (table (driver a).requirements n)
    ((driver a).state n).frozen x

theorem prefix_mass_of_forecast (n : ℕ) (x : (RatFunc ℚ)ˣ)
    (forecast : ∀ p ∉ (driver a).assigned n, ∀ r, (driver a).permanentRole p = some r →
      permanentBranch a x false p = forecastOrder (signed a x).height (some r) ∧ permanentBranch a x true p = 0) :
    (prefixSigned a n x).MassEquations (PrefixProfile.index ((driver a).assigned n) ((driver a).state n).role)
      (PrefixProfile.sign ((driver a).assigned n) ((driver a).state n).role) := by
  let D := driver a
  intro k
  apply Eq.trans _ (signed_mass a x k)
  unfold prefixSigned PrefixProfile.signed PrefixProfile.fromTable
  rw [PrefixProfile.mass_eq, provisional_signedMass]
  change _ = (signed a x).signedMass (massIndexing a).index (massIndexing a).sign k
  rw [MassReindex.signedMass_eq_sum (massIndexing a) (D.assigned n) _ _ _ (actual_reads a x) forecast]
  congr 1
  apply Finset.sum_congr rfl
  intro p hp
  rw [D.role_eq_permanent p hp,branchOrder_at a n x false p hp,branchOrder_at a n x true p hp]
  rfl

theorem prefix_mass_of_exterior (n : ℕ) (x : (RatFunc ℚ)ˣ) (h : Exterior a n x) :
    (prefixSigned a n x).MassEquations (PrefixProfile.index ((driver a).assigned n) ((driver a).state n).role)
      (PrefixProfile.sign ((driver a).assigned n) ((driver a).state n).role) := by
  apply prefix_mass_of_forecast
  intro p hp role hr
  rw [← primary_permanentBranch a _ p (by rw [hr]; rfl),← guard_permanentBranch]
  exact ⟨(h.primary p hp role hr).trans (by cases role <;> rfl),h.guard p hp⟩

/-- Every prefix profile of a nonzero ring element is effective, including
all the default centre and guard values at unassigned regular positions. -/
theorem prefix_effective (n : ℕ) (x : (RatFunc ℚ)ˣ) (hx : x.val ∈ domain (driver a).requirements)
    (hr : PrefixProfile.UniqueRegular ((driver a).assigned n) ((driver a).state n).role) :
    ∀ i, 0 ≤ (prefixSigned a n x).signedValues i := by
  let D := driver a
  have hh : x.val ∈ fullIntersection (valuation a) := domain_eq_intersection a ▸ hx
  have eff (i : Coordinates a) : 0 ≤ order (valuation a i) x.val :=
    (order_nonneg_iff _ x.ne_zero).mpr (integral _ ⟨x.val,hh⟩ i)
  apply PrefixProfile.effective _ _ _ _ _ _ hr (fun c => eff (.centre c))
  · intro p hp hprim
    rw [D.role_eq_permanent p hp] at hprim
    obtain ⟨i,hi⟩ := primary_covers a p hprim
    rw [branchOrder_at a n x false p hp,← primary_permanentBranch a x p hprim,← hi]
    exact eff i
  · intro p hp
    let g := (guardPrime a).symm p
    have h := eff (guardSite g)
    rw [valuation_guard] at h
    change 0 ≤ order (UnivariateExtraction.guardVal D.requirements (guardPrime a g)) x.val at h
    rw [Equiv.apply_symm_apply (guardPrime a) p] at h
    rwa [branchOrder_at a n x true p hp,← guard_permanentBranch]
  · intro q
    obtain ⟨t,_,ht⟩ := D.frozen_iff.mp q.property.1
    let j : Horiz a := ⟨q.val,D.retained t _ ht,q.property.2⟩
    exact (HorizontalOrders.neg_log_valuation_eq_exponents q.val x.val x.ne_zero) ▸ eff (.other (.horizontal j))

end UnconditionalCounterexample.Variations.DyadicLedger.Calibrated
