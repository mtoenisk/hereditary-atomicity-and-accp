import UnconditionalCounterexample.Variations.DyadicRoundCalibration
import UnconditionalCounterexample.Variations.DyadicLedgerCalendar
import UnconditionalCounterexample.Variations.DyadicPermanentRoles

/-! # Permanent calibration and finite exceptions for frozen horizontals -/

noncomputable section
namespace UnconditionalCounterexample.Variations.DyadicLedger

open GuardSupport Univariate RecursivePrefix Polynomial Calibration BulkInputs OpeningCalibration

namespace FreshFibres
variable {n : ℕ} {m : Ledger} {P : Prefix n}

/-- At a new paired fibre the primitive model has its regular-tail order
on the primary and vanishes in additive valuation on the guard. -/
def Predicts (a : FreshFibres m P) (f : FreezingCalendar.Horizontal) : Prop :=
  ∀ p (hp : p ∈ a.births.primes) r, a.role p hp = some r →
    (aeval ((a.births.site p hp).branch false) (model f).poly).valuation =
        forecastOrder (height f.val) (some r) ∧
      (aeval ((a.births.site p hp).branch true) (model f).poly).valuation = 0

theorem predicts_of_unlabelled (a : FreshFibres m P) (h : ∀ p hp, a.role p hp = none)
    (f : FreezingCalendar.Horizontal) : a.Predicts f := by
  intro p hp r hr
  rw [h p hp] at hr
  cases hr

end FreshFibres

namespace OpeningCalibration

theorem Room.predicts_old {n : ℕ} {m : Ledger} {P : Prefix n} {T : Table P.state.assignment.primes}
    {A K : Finset ℚ[X]} {hA : HorizontalSet A} {hK : HorizontalSet K} {bound L : ℕ}
    {B : Phase m P T hA hK bound L} {s : Block} (R : Room B s) (b : FreshFibres m P)
    (use : Installed R.fibres b) (f : FreezingCalendar.Horizontal) (hf : f.val ∈ K) : b.Predicts f :=
  fun p hp r hr => R.old_model_orders b use p hp r hr ⟨f.val,hf⟩

end OpeningCalibration

namespace Driver

/-- Once a horizontal is first frozen, every later stage inherits its
mass from that successor. The only per-stage input concerns the *old*
frozen factors and is supplied by `Room.predicts_old` at openings. -/
theorem frozen_mass (D : Driver) (t : ℕ) (f : FreezingCalendar.Horizontal)
    (hf : f.val ∈ (D.actualRequest t).freeze)
    (calibrated : ∀ k, D.rationalMass (t+1) f.val (height f.val) k = height f.val k)
    (future : ∀ n, f.val ∈ (D.state n).frozen → (D.actualRequest n).toFreshFibres.Predicts f)
    {b : ℕ} (ht : t < b) (k : Bool) :
    D.rationalMass b f.val (height f.val) k = height f.val k := by
  rw [D.rationalMass_eq_model, D.provisionalMass_persistent ht (model f).poly (height f.val) _ k,
    ← D.rationalMass_eq_model]
  · exact calibrated k
  · intro n hn _
    exact future n (D.frozen_iff.mpr ⟨t,hn,hf⟩)

/-- The actual permanent primary and guard orders of this model match
their forecast everywhere except in the finite table at calibration. -/
theorem frozen_orders_outside (D : Driver) (t : ℕ) (f : FreezingCalendar.Horizontal)
    (hf : f.val ∈ (D.actualRequest t).freeze)
    (future : ∀ n, f.val ∈ (D.state n).frozen → (D.actualRequest n).toFreshFibres.Predicts f)
    (p : PrimeIndex) (hp : p ∉ D.assigned (t+1)) (r : FibreRole)
    (hr : D.permanentRole p = some r) :
    (aeval ((permanentSite D.requirements p).branch false) (model f).poly).valuation =
        forecastOrder (height f.val) (some r) ∧
      (aeval ((permanentSite D.requirements p).branch true) (model f).poly).valuation = 0 := by
  obtain ⟨i,hi,he⟩ := (D.permanentRole_iff p r).mp hr
  have ht : t < i := by
    by_contra! h
    apply hp
    exact assigned_mono D.requirements (Nat.succ_le_succ h)
      ((selection D.requirements i).batch.processed_subset_assigned (D.schedule.requested_processed i hi))
  rw [(D.permanent_role (n := i) p hi).1]
  exact future i (D.frozen_iff.mpr ⟨t,ht,hf⟩) p hi r he

/-- Past one explicit finite table the monic rational horizontal takes
the same forecast values as the integral model at both branches. -/
theorem frozen_rational_orders_outside (D : Driver) (t : ℕ) (f : FreezingCalendar.Horizontal)
    (hf : f.val ∈ (D.actualRequest t).freeze)
    (future : ∀ n, f.val ∈ (D.state n).frozen → (D.actualRequest n).toFreshFibres.Predicts f)
    (p : PrimeIndex) (hp : p ∉ D.assigned (max (t+1) (scalarBound f))) (r : FibreRole)
    (hr : D.permanentRole p = some r) : Orders (permanentSite D.requirements p) r f.val := by
  let s := permanentSite D.requirements p
  have hlate : scalarBound f < p.val := by
    by_contra! h
    exact hp (assigned_mono D.requirements (h.trans (le_max_right _ _)) (D.assigned_prime p))
  have hold := D.frozen_orders_outside t f hf future p
    (fun he => hp (assigned_mono D.requirements (le_max_left _ _) he)) r hr
  have hnorm := unit_scalar f p hlate
  have hscalar := EvaluationChoices.valuation_eq_of_norm_eq p.val
    (Rat.cast_ne_zero.mpr (model f).scalar_ne) (one_ne_zero : (1 : ℚ_[p.val]) ≠ 0)
    (hnorm.trans norm_one.symm)
  have paired := (D.paired_iff_role p).mpr (by rw [hr]; rfl)
  have he (b : Bool) : (aeval (s.branch b) (model f).poly).valuation =
      (aeval (s.branch b) f.val).valuation := by
    have hne : aeval (s.branch b) f.val ≠ 0 :=
      mt (transcendental_iff.mp (s.branch_transcendental b (Or.inr paired)) f.val) f.property.1.ne_zero
    rw [model_eval, Padic.valuation_mul (Rat.cast_ne_zero.mpr (model f).scalar_ne) hne,
      hscalar, Padic.valuation_one, zero_add]
  exact ⟨(he false).symm.trans hold.1, (he true).symm.trans hold.2⟩

end Driver
end UnconditionalCounterexample.Variations.DyadicLedger
