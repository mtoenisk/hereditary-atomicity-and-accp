import UnconditionalCounterexample.Variations.DyadicPrefixMass
import UnconditionalCounterexample.Variations.DyadicFiniteProfiles

/-! # Calibration of the coarse factors at an actual split opening -/

noncomputable section
namespace UnconditionalCounterexample.Variations.DyadicLedger.Calibrated
open Polynomial GuardSupport Univariate FreezingCalendar DiscreteOrders DyadicDeviations DyadicSplit OpeningCalibration Calibration

variable (a : Policy)

theorem prefix_uniqueRegular (n : ℕ) :
    let D := driver a
    PrefixProfile.UniqueRegular (D.assigned n) (D.state n).role := by
  let D := driver a
  dsimp only
  intro p hp q hq c k i hpr hqr
  exact D.permanent_regular_unique ((D.role_eq_permanent p hp).symm.trans hpr)
    ((D.role_eq_permanent q hq).symm.trans hqr)

theorem prefix_paired (n : ℕ) (p : PrimeIndex) (hp : p ∈ (driver a).assigned n)
    (hr : (((driver a).state n).role p).isSome) : (table (driver a).requirements n p hp).paired := by
  rw [table_eq_permanentSite]
  obtain ⟨s,hs⟩ := Option.isSome_iff_exists.mp hr
  exact (driver a).paired_of_role p hs

private theorem centre_eq (c : Bool) : PrefixProfile.centre c = centre c := by cases c <;> rfl

theorem prefix_centre_frozen (n : ℕ) (hn : 0 < n) (c : Bool) :
    (PrefixProfile.centre c).val ∈ ((driver a).state n).frozen := by
  let D := driver a
  apply D.frozen_iff.mpr
  refine ⟨0,hn,?_⟩
  have h := dispatcher_calendar (planner a) 0
  change D.openingFreeze 0 ∅ = (D.actualRequest 0).freeze at h
  rw [← h]
  cases c
  · exact (initially_both ∅).1
  · exact (initially_both ∅).2

theorem prefix_horizontal_mass (n : ℕ) (K : Finset ℚ[X]) (f : Horizontal)
    (hf : f.val ∈ ((driver a).state n).frozen) :
    let D := driver a; let A := D.assigned n; let r := (D.state n).role
    (PrefixProfile.signed A r (table D.requirements n) K (DyadicSplit.horizontalUnit f)).MassEquations
      (PrefixProfile.index A r) (PrefixProfile.sign A r) := by
  let D := driver a
  let A := D.assigned n
  let roles := (D.state n).role
  let T := table D.requirements n
  let x := DyadicSplit.horizontalUnit f
  let ht (c : Bool) := order (HorizontalOrders.valuation (PrefixProfile.centre c)) x.val
  have he : ht = height f.val := funext fun c => by
    dsimp only [ht]
    rw [centre_eq]
    exact centre_order_horizontal c f
  obtain ⟨t,htn,hf'⟩ := D.frozen_iff.mp hf
  dsimp only
  intro k
  change (PrefixProfile.preview A roles ht _ _ _).signedMass _ _ k = (ht k : ℚ)
  rw [PrefixProfile.mass_eq,provisional_signedMass,he]
  apply Eq.trans _ (permanent_mass a f hf' htn k)
  simp only [Driver.rationalMass,provisional_signedMass]
  congr 1
  apply Finset.sum_congr rfl
  intro p hp
  change discrepancy (roles p) (height f.val) k _ _ = discrepancy (roles p) (height f.val) k _ _
  cases hr : roles p with
  | none => rfl
  | some r =>
    have paired := prefix_paired a n p hp (show (roles p).isSome from by simp [hr])
    have br (b : Bool) : PrefixProfile.branchOrder A T x.val b p = D.rationalOrder n f.val b p := by
      have hb : MixedStageSelection.Active (T p hp).paired b := Or.inr paired
      have hp' : p ∈ ((chain D.requirements).approx n).state.assignment.primes := hp
      simp only [PrefixProfile.branchOrder,Driver.rationalOrder,hp,hp',↓reduceDIte,branchValue,hb]
      exact congrArg Padic.valuation (ReturnTargets.evaluationHom_polynomial p.val _ _ f.val)
    rw [br,br]

/-- Every coarse factor computed at a positive stage satisfies the two finite
mass equations, using just the factors already frozen by this same ledger. -/
theorem prefix_coarse_mass (n : ℕ) (hn : 0 < n)
    (u : Profile (PrefixProfile.Aux ((driver a).assigned n) ((driver a).state n).role)
      (PrefixProfile.Lone ((driver a).assigned n) ((driver a).state n).role)
      (PrefixProfile.Known ((driver a).state n).frozen)) :
    let D := driver a; let A := D.assigned n; let r := (D.state n).role
    let T := table D.requirements n; let K := (D.state n).frozen
    (PrefixProfile.signed A r T K (PrefixProfile.coarse A r T K u)).MassEquations
      (PrefixProfile.index A r) (PrefixProfile.sign A r) := by
  apply PrefixProfile.coarse_mass _ _ _ _ (prefix_uniqueRegular a n) (prefix_paired a n)
  intro i
  apply prefix_horizontal_mass
  cases i with
  | inl c => exact prefix_centre_frozen a n hn c
  | inr j => exact j.property.1

end UnconditionalCounterexample.Variations.DyadicLedger.Calibrated
