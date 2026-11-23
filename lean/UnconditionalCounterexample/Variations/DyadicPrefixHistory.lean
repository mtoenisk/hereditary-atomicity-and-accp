import UnconditionalCounterexample.Variations.DyadicAuxiliaryEmission
import UnconditionalCounterexample.Variations.DyadicPrefixInstruction

/-! # Every exponent in a prepared word has been emitted by its reserved stage -/

noncomputable section
namespace UnconditionalCounterexample.Variations.DyadicLedger.Calibrated
open GuardSupport Univariate DyadicEscape DyadicBlocks PrefixInstruction

variable (a : Policy)

/-- An auxiliary prime already on the opening table has its own selected raw
strictly before this opening. Its emitting block is its unique birth block. -/
theorem prefix_auxiliary_emitted (r : ℕ) (k : Bool) (j : Aux a k)
    (hp : j.prime ∈ (driver a).assigned ((driver a).opening r)) :
    ∃ n < (driver a).opening r, ((driver a).actualRequest n).column =
      .auxiliary j.prime k j.index j.positive := by
  let E := emission a
  let D := driver a
  obtain ⟨n,hc⟩ := auxiliary_emitted a k j
  refine ⟨n,?_,hc⟩
  rcases E.exhaustive n with ⟨s,i,hstage,he⟩ | ⟨g,_,he⟩
  · obtain ⟨q,l,idx,sign,hbirth,hq,_⟩ := (recorded a).allocated s _ (List.getElem_mem (h := i.isLt))
    have eqp := (RawColumn.auxiliary.inj (hc.symm.trans (he.trans hq))).1
    subst q
    have early : s < r := by
      by_contra! hn
      exact (D.actualRequest (D.opening s)).births.fresh _ hbirth
        (assigned_mono D.requirements (D.opening_strict.monotone hn) hp)
    have hs : n < D.opening (s+1) := by
      rw [← E.stage_boundary]
      have hb := (locate_bounds E.rounds.length_pos n).2
      have hl : locate E.rounds.length_pos n = s := (congrArg (locate E.rounds.length_pos) hstage.symm).trans
        (E.rounds.auxiliary_round s i)
      rwa [hl] at hb
    exact hs.trans_le (D.opening_strict.monotone early)
  · cases g <;> cases hc.symm.trans he

/-- The regular width is chosen after computing the finite exponents. Together
with the earlier auxiliary emissions this covers the actual polynomial
history through the reserved final raw. -/
theorem prefix_coefficients_emitted (r : ℕ) (x : (RatFunc ℚ)ˣ) (aux : List RawColumn)
    (w : Prepared ((driver a).state ((driver a).opening r))
      ((chain (driver a).requirements).approx ((driver a).opening r))
      (table (driver a).requirements ((driver a).opening r)) aux x)
    (hblock : (emission a).block r = w.block) :
    w.exponents.support ⊆ (Finset.range (((driver a).opening (r+1)-1)+1)).image
      (fun i => ((driver a).actualRequest i).column) := by
  let D := driver a
  let E := emission a
  let n := D.opening r
  let A := D.assigned n
  let role := (D.state n).role
  have hnext : 0 < D.opening (r+1) := Nat.zero_lt_of_lt (D.opening_strict (Nat.lt_succ_self r))
  have hlast : D.opening (r+1)-1+1 = D.opening (r+1) := by omega
  intro c hc
  apply Finset.mem_image.mpr
  obtain ⟨g,hg⟩ := w.basis c hc
  have hbelow := w.support_below c hc
  cases g with
  | inl g =>
    have heb : Emission.regularColumn g = c := by cases g <;> exact hg
    refine ⟨E.rounds.regularStage g,Finset.mem_range.mpr ?_,(E.regular g).trans heb⟩
    rw [hlast,← E.stage_boundary]
    have upper : (D.state n).regularBound + w.block.width = boundary E.rounds.width (r+1) := by
      rw [boundary,E.index_boundary,E.start]
      change _ + _ = _ + (E.block r).width
      rw [hblock]
    cases g with
    | balanced k i =>
      subst c
      exact (E.rounds.regular_before_boundary (r+1) k i (upper ▸ hbelow)).2
    | adjacent k i =>
      subst c
      exact (E.rounds.regular_before_boundary (r+1) k i (upper ▸ hbelow)).1
  | inr j =>
    obtain ⟨k,j⟩ := j
    obtain ⟨i,e,hr⟩ := j.property.2
    change role j.val = some (.auxiliary k i e) at hr
    have index_eq : PrefixProfile.index A role k j = i := by
      simp [PrefixProfile.index,Calibration.auxWeight,hr,FibreRole.index]
    have positive_eq : PrefixProfile.positive A role k j = e := by
      cases e <;> simp [PrefixProfile.positive,Calibration.auxSign,hr,FibreRole.sign]
    let q : Aux a k := ⟨j.val,i,e,((D.role_eq_permanent _ j.property.1).symm.trans hr)⟩
    obtain ⟨t,ht,hcol⟩ := prefix_auxiliary_emitted a r k q j.property.1
    have hb : t < D.opening (r+1)-1+1 := by rw [hlast]; exact ht.trans (D.opening_strict (Nat.lt_succ_self r))
    refine ⟨t,Finset.mem_range.mpr hb,hcol.trans ?_⟩
    change RawColumn.auxiliary j.val k (PrefixProfile.index A role k j) (PrefixProfile.positive A role k j) = c at hg
    rw [index_eq,positive_eq] at hg
    exact hg

end UnconditionalCounterexample.Variations.DyadicLedger.Calibrated
