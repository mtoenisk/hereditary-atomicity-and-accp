import UnconditionalCounterexample.MixedConstructionWords
import UnconditionalCounterexample.ReturnPrefix

/-! Normalization and refined returns for the very same mixed-stage Choice.
All assertions are restricted to actual active branches. -/

noncomputable section
namespace UnconditionalCounterexample.MixedReturnPrefix
open Polynomial ConstructionWords

theorem choice_actual_norm {ι : Type*} [Fintype ι]
    (p : ι → ℕ) [∀ i, Fact (p i).Prime] (paired : ι → Prop) (ell : ℕ) [Fact ell.Prime]
    (m : ℕ) (P : RecursivePrefix.Prefix m)
    (plan : DegreePlan m P.rawAt P.exponentAt)
    (x v : ∀ i, Bool → ℚ_[p i])
    (hx : ∀ i b, MixedStageSelection.Active (paired i) b → Transcendental ℚ (x i b))
    (kv : ι → Bool → ℕ) (choice : MixedConstructionWords.Choice p paired ell plan x v kv)
    (S : RecursivePrefix.Next P)
    (hraw : S.raw = ShiftedEisenstein.monicFamily (plan.degree - 1)
      (SignedConstant.constant p choice.N (plan.degree - 1 + 1)) choice.coeff)
    (hE : S.exponent = plan.E) :
    ∀ i b (hb : MixedStageSelection.Active (paired i) b),
      ‖EvaluationDVR.evaluationHom (p i) (x i b) (hx i b hb) (S.append.generators m)‖ = ‖v i b‖ := by
  intro i β hβ
  let c := SignedConstant.constant p choice.N (plan.degree - 1 + 1)
  let F := ShiftedEisenstein.monicFamily (plan.degree - 1) c choice.coeff
  have hQ : S.append.generators m = algebraMap ℚ[X] (RatFunc ℚ) F /
      algebraMap ℚ[X] (RatFunc ℚ) plan.rawDen := by
    rw [S.generators_last, hraw, hE]
    rfl
  have hmap := ShiftedEisenstein.monicFamily_map (algebraMap ℚ ℚ_[p i])
    (plan.degree - 1) c choice.coeff
  have hcast (r : ℚ) : algebraMap ℚ ℚ_[p i] r = (r : ℚ_[p i]) := by
    simpa only [Rat.cast_id] using map_ratCast (algebraMap ℚ ℚ_[p i]) r
  simp only [hcast] at hmap
  have hn := (((choice.witnesses.2.2.2.2.2.1 i).2).1 β hβ).2.1
  change ‖(ShiftedEisenstein.monicFamily (plan.degree - 1) (c : ℚ_[p i])
    (fun j => (choice.coeff j : ℚ_[p i]))).eval (x i β) /
      plan.rawDen.eval₂ (algebraMap ℚ ℚ_[p i]) (x i β)‖ = ‖v i β‖ at hn
  rw [← hmap, Polynomial.eval_map] at hn
  rw [hQ, ReturnTargets.evaluation_normalized_polynomial]
  exact hn

/-- The q-stage only needs target and precision identities on active entries;
unused primary entries at an omitted prime impose no condition. -/
theorem choice_q_actual {ι : Type*} [Fintype ι]
    (p : ι → ℕ) [∀ i, Fact (p i).Prime] (paired : ι → Prop) (ell : ℕ) [Fact ell.Prime]
    (n : ℕ) (P : RecursivePrefix.Prefix (2 * n + 2))
    (plan : DegreePlan (2 * n + 2) P.rawAt P.exponentAt)
    (x v : ∀ i, Bool → ℚ_[p i])
    (hx : ∀ i b, MixedStageSelection.Active (paired i) b → Transcendental ℚ (x i b))
    (h kv : ι → Bool → ℕ) (choice : MixedConstructionWords.Choice p paired ell plan x v kv)
    (hv : ∀ i b (hb : MixedStageSelection.Active (paired i) b),
      v i b = P.qTarget n (p i) (x i b) (hx i b hb) (h i b))
    (hkv : ∀ i b (hb : MixedStageSelection.Active (paired i) b),
      kv i b = P.qPrecision n (p i) (x i b) (hx i b hb) (h i b))
    (S : RecursivePrefix.Next P)
    (hraw : S.raw = ShiftedEisenstein.monicFamily (plan.degree - 1)
      (SignedConstant.constant p choice.N (plan.degree - 1 + 1)) choice.coeff)
    (hE : S.exponent = plan.E) :
    ∀ i b (hb : MixedStageSelection.Active (paired i) b),
      (ReturnTargets.IsRefined (h i b)
        (EvaluationDVR.evaluationHom (p i) (x i b) (hx i b hb) (P.a n * P.b (n + 1))) →
        (EvaluationDVR.evaluationHom (p i) (x i b) (hx i b hb) (S.append.a (n + 1)) - 1) /
          (p i : ℚ_[p i]) ^ n ∈ PadicInt.subring (p i)) := by
  intro i β hβ href
  let c := SignedConstant.constant p choice.N (plan.degree - 1 + 1)
  let F := ShiftedEisenstein.monicFamily (plan.degree - 1) c choice.coeff
  have hA : S.append.a (n + 1) = ReturnTargets.nextReturn (P.a n) (P.b (n + 1))
      (algebraMap ℚ[X] (RatFunc ℚ) F / algebraMap ℚ[X] (RatFunc ℚ) plan.rawDen) := by
    rw [S.a_succ_at_q, hraw, hE]
    rfl
  have hr := (((choice.witnesses.2.2.2.2.2.1 i).2).1 β hβ).2.2
  change (v i β /
    ((ShiftedEisenstein.monicFamily (plan.degree - 1) (c : ℚ_[p i])
      (fun j => (choice.coeff j : ℚ_[p i]))).eval (x i β) /
      plan.rawDen.eval₂ (algebraMap ℚ ℚ_[p i]) (x i β)) - 1) /
        (p i : ℚ_[p i]) ^ kv i β ∈ PadicInt.subring (p i) at hr
  have heval :
      (ShiftedEisenstein.monicFamily (plan.degree - 1) (c : ℚ_[p i])
        (fun j => (choice.coeff j : ℚ_[p i]))).eval (x i β) =
      F.eval₂ (algebraMap ℚ ℚ_[p i]) (x i β) := by
    have hmap := ShiftedEisenstein.monicFamily_map (algebraMap ℚ ℚ_[p i])
      (plan.degree - 1) c choice.coeff
    have hcast (r : ℚ) : algebraMap ℚ ℚ_[p i] r = (r : ℚ_[p i]) := by
      simpa only [Rat.cast_id] using map_ratCast (algebraMap ℚ ℚ_[p i]) r
    simp only [hcast] at hmap
    rw [← hmap, Polynomial.eval_map]
  rw [heval, hv i β hβ, hkv i β hβ] at hr
  rw [hA]
  exact ReturnTargets.actual_refined_return (p i) (x i β) (hx i β hβ)
    (P.a n) (P.b (n + 1)) F plan.rawDen n (h i β) href hr

end UnconditionalCounterexample.MixedReturnPrefix
