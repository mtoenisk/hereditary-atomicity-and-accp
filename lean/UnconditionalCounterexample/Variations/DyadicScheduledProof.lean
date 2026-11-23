import UnconditionalCounterexample.Variations.DyadicScheduledTask
import UnconditionalCounterexample.Variations.DyadicInstalledSplit
import UnconditionalCounterexample.Variations.DyadicSourceEligibility
import UnconditionalCounterexample.Variations.DyadicFinalTransfer

/-! # From a permanent split profile to the actual coprime factors -/

noncomputable section
namespace UnconditionalCounterexample.Variations.DyadicLedger.ScheduledSplit
open GuardSupport Univariate Calibrated DiscreteOrders DyadicDeviations

abbrev policy : Calibrated.Policy := PrefixInstruction.policy

/-- Permanent field profiles of the two proposed factors and the signed column
identity for the first one. -/
def Profiled (r : ℕ) (hx : (taskAt r).element ≠ 0) (w : PreparedAt r hx) : Prop :=
  let I := w.instruction (taskAt r)
  ∃ u v : Profile (Aux policy) (Lone policy) (Horiz policy),
    SplitAt (auxIndex policy) (auxSign (auxPositive policy)) (signed policy (Units.mk0 _ hx)) u v I.index ∧
      (signed policy I.coarse).translate (auxIndex policy) (auxSign (auxPositive policy))
        (columnsOfRaw (auxiliaryPrime policy) (auxIndex policy) (auxPositive policy) I.coefficients) = u

theorem hasSplits_of_profiled (physical : ∀ r hx (w : PreparedAt r hx), Profiled r hx w) :
    HasSplits policy (domain run.requirements) := by
  intro x m hx hm h₀ h₁
  obtain ⟨r,he,hmod⟩ := named x.val hm
  have hn : (taskAt r).element ≠ 0 := he ▸ hx
  have hp : Nonempty (PreparedAt r hn) := task_has_prepared policy r hn (he ▸ x.property)
    (he ▸ h₀) (he ▸ h₁) (aux r)
  obtain ⟨w,hLayout,hI⟩ := installs r hn hp
  let I := w.instruction (taskAt r)
  obtain ⟨u,v,hsplit,ht⟩ := physical r hn w
  have hunit : Units.mk0 (taskAt r).element hn = Units.mk0 x.val hx := Units.ext he
  have hsplit' := (congrArg (fun Z => SplitAt (auxIndex policy) (auxSign (auxPositive policy))
    (signed policy Z) u v I.index) hunit).mp hsplit
  obtain ⟨U,V,d,e,hx',hU,hV,hm',hcop,hd,he'⟩ := coprime_factors_of_installed policy
    (signed policy) (signed_values policy) (r+1) I hI rfl x hx he u v hsplit' ht
    (precedes r hn w hLayout) (modulus_roles r hn w)
  exact ⟨U,V,d,e,hx',hU,hV,hmod.symm.trans hm',hcop,hd,he'⟩

end UnconditionalCounterexample.Variations.DyadicLedger.ScheduledSplit
