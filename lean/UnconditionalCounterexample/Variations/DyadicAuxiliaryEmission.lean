import UnconditionalCounterexample.Variations.DyadicConcreteCoordinates

/-! # Every auxiliary birth emits its own weighted generator -/

noncomputable section
namespace UnconditionalCounterexample.Variations.DyadicLedger.Calibrated
open GuardSupport Univariate
variable (a : Policy)

/-- The auxiliary prime was born at an opening. Its own weighted raw
occurs in that opening's block and is actually consumed by the driver. -/
theorem auxiliary_emitted (k : Bool) (j : Aux a k) :
    ∃ i, ((driver a).actualRequest i).column = .auxiliary j.prime k j.index j.positive := by
  let D := driver a
  obtain ⟨t,hp,hr⟩ := (D.permanentRole_iff j.prime _).mp j.role_eq
  have ht : (D.state t).remaining = [] := by
    by_contra hn
    have h := (dispatch_interior_roles (planner a) (D.state t) ((chain D.requirements).approx t)
      (table D.requirements t) hn).2 j.prime hp
    have absurd : (none : Option FibreRole) = some (.auxiliary k j.index j.positive) := h.symm.trans hr
    cases absurd
  have hc := ((actualRoom a t).auxiliary_iff _ (installed a t ht) j.prime k j.index j.positive).mp
    ⟨hp,hr⟩
  have hc' : RawColumn.auxiliary j.prime k j.index j.positive ∈ (actualLayout a t).block.auxiliary := by
    rwa [(actualLayout a t).auxiliary_eq]
  have hblock : (D.actualRequest t).openBlock = (actualLayout a t).block.columns :=
    (dispatcher_open (planner a) (D.state t) ((chain D.requirements).approx t)
      (table D.requirements t) ht).1
  have mem : RawColumn.auxiliary j.prime k j.index j.positive ∈ (D.actualRequest t).openBlock := by
    rw [hblock,Block.columns]
    exact List.mem_append_left _ (List.mem_append_left _ hc')
  obtain ⟨i,hi⟩ := List.mem_iff_getElem?.mp mem
  exact ⟨t+i,D.emits_at_empty t ht hi⟩

end UnconditionalCounterexample.Variations.DyadicLedger.Calibrated
