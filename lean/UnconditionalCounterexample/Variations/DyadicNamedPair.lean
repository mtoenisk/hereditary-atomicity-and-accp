import UnconditionalCounterexample.Variations.DyadicConcreteRealization

/-! # The two named witnesses in the selected rational-function domain -/

noncomputable section
namespace UnconditionalCounterexample.Variations.DyadicLedger.Calibrated
open Univariate DiscreteOrders DyadicProfiles

variable (a : Policy)

/-- The first element has an early plus entry of two at index zero. The
second has an early plus entry of four at index one. -/
def pairElement (second : Bool) : domain (driver a).requirements :=
  (RingEquiv.subringCongr (domain_eq_intersection a)).symm ((realization a).pairEntry second)

theorem pairElement_ne_zero (second : Bool) : pairElement a second ≠ 0 := by
  intro h
  have hv := congrArg (fun z : domain (driver a).requirements => z.val) h
  exact ((realization a).pairEntry_spec second).1 (Subtype.ext hv)

/-- All coordinates, including every supplementary zero, of each witness. -/
theorem pairElement_values (second : Bool) (i : Coordinates a) :
    natOrder (valuation a i) (pairElement a second : RatFunc ℚ) = (witness second).values 0 i :=
  (realization_values a _ i).symm.trans (congrFun ((realization a).pairEntry_spec second).2 i)

theorem pairElement_extend {d : domain (driver a).requirements}
    (hx : d ∣ pairElement a false) (hy : d ∣ pairElement a true) :
    ∃ u, ¬ IsUnit u ∧ d*u ∣ pairElement a false ∧ d*u ∣ pairElement a true := by
  let e := RingEquiv.subringCongr (domain_eq_intersection a)
  have div (b : Bool) (h : d ∣ pairElement a b) : e d ∣ (realization a).pairEntry b := by
    simpa only [pairElement,← show RingEquiv.subringCongr (domain_eq_intersection a) = e from rfl,
      RingEquiv.apply_symm_apply] using map_dvd e h
  obtain ⟨v,hv,hx',hy'⟩ := (realization a).pair_extension (div false hx) (div true hy)
  refine ⟨e.symm v,fun h => hv (by simpa using h.map e),?_,?_⟩
  · change d*e.symm v ∣ e.symm ((realization a).pairEntry false)
    simpa only [map_mul,RingEquiv.symm_apply_apply] using map_dvd e.symm hx'
  · change d*e.symm v ∣ e.symm ((realization a).pairEntry true)
    simpa only [map_mul,RingEquiv.symm_apply_apply] using map_dvd e.symm hy'

end UnconditionalCounterexample.Variations.DyadicLedger.Calibrated
