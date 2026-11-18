import UnconditionalCounterexample.LocalStageSelection
import UnconditionalCounterexample.SingleLocalInterpolation
import UnconditionalCounterexample.LocalAlgebra.SingleScaledTransfer

/-!
# A single coefficient neighborhood at an unpaired guard

The target at beta has prescribed normalized value B*v and fixed constant c.
One coefficient ball preserves that value's norm, return congruence, every
listed derivative bound, and all scaled coefficient comparisons. These are
conditions on the same later monic polynomial; no polynomial is chosen here.
-/

noncomputable section
namespace UnconditionalCounterexample.SingleLocalStageSelection

open Polynomial

theorem localTarget_eq_monicFamily {K : Type*} [Field K]
    (β η : K) (n : ℕ) (c : K) (hn : 1 < n + 1) :
    ShiftedEisenstein.monicFamily n c
      (fun j => (SingleLocalInterpolation.localTarget β η (n + 1) c).coeff (j.val + 1)) =
      SingleLocalInterpolation.localTarget β η (n + 1) c := by
  have hT := SingleLocalInterpolation.localTarget_monic_degree β η (n + 1) c hn
  apply ShiftedEisenstein.monicFamily_eq _ _ _ _ hT.monic hT.natDegree_eq
  · rw [coeff_zero_eq_eval_zero]
    exact SingleLocalInterpolation.localTarget_eval_zero β η (n + 1) c (by omega)
  · intro j
    rfl

def ConditionsAtPrime {W : Type*} (p : ℕ) [Fact p.Prime]
    (n stage : ℕ) (c : ℚ_[p]) (q0 q : Fin n → ℚ_[p]) (β B v : ℚ_[p]) (kv : ℕ)
    (t : Finset W) (H : W → ℚ_[p][X]) (a : W → ℕ) : Prop :=
  ((ShiftedEisenstein.monicFamily n c q).eval β ≠ 0 ∧
    ‖(ShiftedEisenstein.monicFamily n c q).eval β / B‖ = ‖v‖ ∧
    (v / ((ShiftedEisenstein.monicFamily n c q).eval β / B) - 1) /
      (p : ℚ_[p]) ^ kv ∈ PadicInt.subring p) ∧
  (∀ w ∈ t, (LocalInterpolation.wordDerivative (ShiftedEisenstein.monicFamily n c q)
      (H w) (a w) β).valuation < -(stage : ℤ)) ∧
  (∀ s : ℕ, s ≤ stage → ∀ j : ℕ,
    (C c⁻¹ * (ShiftedEisenstein.monicFamily n c q - ShiftedEisenstein.monicFamily n c q0).comp
      (C (((p : ℚ_[p]) ^ s)⁻¹) * X)).coeff j /
        (p : ℚ_[p]) ^ stage ∈ PadicInt.subring p)

theorem exists_local_target_tolerance {W : Type*}
    (p : ℕ) [Fact p.Prime] (n stage : ℕ) (hn : 1 < n + 1) (c : ℚ_[p])
    (β B v : ℚ_[p]) (kv : ℕ) (hβ : β ≠ 0) (hB : B ≠ 0) (hv : v ≠ 0)
    (t : Finset W) (H : W → ℚ_[p][X]) (a : W → ℕ)
    (hword : ∀ w ∈ t, (p : ℝ) ^ stage < ‖LocalInterpolation.wordDerivative
      (SingleLocalInterpolation.localTarget β (B * v) (n + 1) c) (H w) (a w) β‖) :
    let q0 : Fin n → ℚ_[p] := fun j =>
      (SingleLocalInterpolation.localTarget β (B * v) (n + 1) c).coeff (j.val + 1)
    ∃ δ : ℝ, 0 < δ ∧ ∀ q : Fin n → ℚ_[p], (∀ j, ‖q j - q0 j‖ < δ) →
      ConditionsAtPrime p n stage c q0 q β B v kv t H a := by
  classical
  dsimp only
  let T := SingleLocalInterpolation.localTarget β (B * v) (n + 1) c
  let q0 : Fin n → ℚ_[p] := fun j => T.coeff (j.val + 1)
  have hT : ShiftedEisenstein.monicFamily n c q0 = T := localTarget_eq_monicFamily β _ n c hn
  have htarget : (ShiftedEisenstein.monicFamily n c q0).eval β = B * v := by
    rw [hT]
    exact SingleLocalInterpolation.localTarget_eval β _ _ _ hβ
  obtain ⟨δ, hδ, hstable⟩ := CoefficientStability.exists_padic_stage_tolerance_full
    n c q0 (Finset.univ : Finset Unit) (fun _ => β) (fun _ => B) (fun _ => v) (fun _ => kv)
    (fun _ _ => hB) (fun _ _ => hv) (fun _ _ => htarget)
    t (fun _ => β) H a (fun _ => (p : ℝ) ^ stage)
    (fun w hw => by rw [hT]; exact hword w hw)
    (Finset.range (stage + 1)) (fun _ => c⁻¹) (fun s => ((p : ℚ_[p]) ^ s)⁻¹) (fun _ => stage)
  refine ⟨δ, hδ, ?_⟩
  intro q hq
  obtain ⟨hval, hwords, hcoeff⟩ := hstable q hq
  refine ⟨hval () (Finset.mem_univ ()), ?_, ?_⟩
  · intro w hw
    exact SignedConstant.valuation_lt_neg_of_pow_lt_norm p _ stage (hwords w hw)
  · intro s hs j
    exact hcoeff s (Finset.mem_range.mpr (by omega)) j

/-- The same q satisfying the coefficient ball gives actual two-term transfer
for the single linear factor at beta. -/
theorem word_transfer_of_local_conditions {W E : Type*} [Field E]
    (p : ℕ) [Fact p.Prime] (ι : ℚ_[p] →+* E) (t : E)
    (n stage : ℕ) (hn : 1 < n + 1) (c : ℚ_[p]) (hc : c ≠ 0)
    (hcinv : c⁻¹ ∈ PadicInt.subring p) (q : Fin n → ℚ_[p])
    (β B v : ℚ_[p]) (kv : ℕ) (hβ : β ≠ 0) (hβO : β ∈ PadicInt.subring p)
    (ws : Finset W) (H : W → ℚ_[p][X]) (a : W → ℕ)
    (hclear : LocalStageSelection.ClearedAtPrime p stage c
      (SingleLocalInterpolation.fixedRemainder β (B * v) (n + 1)) ws H)
    (hcond : ConditionsAtPrime p n stage c
      (fun j => (SingleLocalInterpolation.localTarget β (B * v) (n + 1) c).coeff (j.val + 1))
      q β B v kv ws H a)
    (s : ℕ) (hs : s ≤ stage) (w : W) (hw : w ∈ ws)
    (ha : 0 < a w) (hH : (H w).eval₂ ι t ≠ 0) :
    ∃ U V : LocalAlgebra.scaledPolynomialRing (PadicInt.subring p) ι (ι (p : ℚ_[p]) ^ s * t),
      (ι (p : ℚ_[p]) ^ (2 * s) * (t - ι β)) ^ a w =
        ι (p : ℚ_[p]) ^ stage * ((U : E) + (V : E) *
          ((ShiftedEisenstein.monicFamily n c q).eval₂ ι t ^ a w / (H w).eval₂ ι t)) := by
  apply LocalAlgebra.scaled_single_word_transfer (PadicInt.subring p) ι t (p : ℚ_[p]) c
    β (B * v) (n + 1) s stage (a w) (ShiftedEisenstein.monicFamily n c q) (H w)
    (Nat.cast_ne_zero.mpr (show p.Prime from Fact.out).ne_zero) (by simp)
    hβ hβO hc hcinv ha hH ?_ ((hclear s hs).1) ((hclear s hs).2 w hw)
  intro j
  rw [← localTarget_eq_monicFamily β (B * v) n c hn]
  have h := hcond.2.2 s hs j
  rw [coeff_C_mul, mul_comm c⁻¹, ← div_eq_mul_inv] at h
  exact h

end UnconditionalCounterexample.SingleLocalStageSelection
