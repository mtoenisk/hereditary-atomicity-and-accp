import UnconditionalCounterexample.SignedConstant
import UnconditionalCounterexample.LocalInterpolation
import UnconditionalCounterexample.CoefficientStability

/-!
# Preparing all local data for one polynomial stage

This joins the exact two-point interpolation, simultaneous signed constant
selection, and coefficient perturbation lemmas for Proposition 3.1. It chooses the common denominator clearings for fixed J/H,
then one rational constant with `N ≥ h + stage`, then positive coefficient balls
preserving every local condition. The prepared balls constrain a single later
choice by the rational approximation and geometric-avoidance theorem; no
independent polynomial is selected for different local requirements.
-/

noncomputable section
open Polynomial
namespace UnconditionalCounterexample.LocalStageSelection

/-- The actual two-point local target belongs to the full fixed-constant monic family. -/
theorem localTarget_eq_monicFamily {K : Type*} [Field K]
    (a b u v : K) (n : ℕ) (c : K) (ha : a ≠ 0) (hb : b ≠ 0) (hn : 2 < n + 1) :
    ShiftedEisenstein.monicFamily n c
      (fun j => (LocalInterpolation.localTarget a b u v (n + 1) c).coeff (j.val + 1)) =
      LocalInterpolation.localTarget a b u v (n + 1) c := by
  have hT := LocalInterpolation.localTarget_monic_degree a b u v (n + 1) c hn
  apply ShiftedEisenstein.monicFamily_eq _ _ _ _ hT.monic hT.natDegree_eq
  · rw [coeff_zero_eq_eval_zero]
    exact LocalInterpolation.localTarget_eval_zero a b u v (n + 1) c ha hb (by omega)
  · intro j
    rfl

/-- One actual local denominator clearing handles J and every listed H at all
scales already scheduled, including s=0 and the first stage. -/
theorem exists_clearing_for_scales {W : Type*}
    (p : ℕ) [Fact p.Prime] (stage : ℕ) (J : ℚ_[p][X])
    (t : Finset W) (H : W → ℚ_[p][X]) :
    ∃ h : ℕ, ∀ s : ℕ, s ≤ stage →
      (∀ k : ℕ, ‖(J.comp (C (((p : ℚ_[p]) ^ s)⁻¹) * X)).coeff k‖ ≤ (p : ℝ) ^ h) ∧
      (∀ w ∈ t, ∀ k : ℕ,
        ‖((H w).comp (C (((p : ℚ_[p]) ^ s)⁻¹) * X)).coeff k‖ ≤ (p : ℝ) ^ h) := by
  classical
  let t' : Finset (Option W × ℕ) :=
    (insert none (t.image some)).product (Finset.range (stage + 1))
  let F : Option W × ℕ → ℚ_[p][X] := fun ws =>
    (ws.1.elim J H).comp (C (((p : ℚ_[p]) ^ ws.2)⁻¹) * X)
  obtain ⟨h, hh⟩ := SignedConstant.exists_polynomial_clearing_exponent p t' F
  refine ⟨h, ?_⟩
  intro s hs
  have hsmem : s ∈ Finset.range (stage + 1) := Finset.mem_range.mpr (by omega)
  constructor
  · intro k
    exact (hh (none, s) (by simp [t', hsmem]) k).1
  · intro w hw k
    exact (hh (some w, s) (by simp [t', hsmem, hw]) k).1

/-- The concrete local conditions preserved by the finite coefficient ball. -/
def ConditionsAtPrime {W : Type*} (p : ℕ) [Fact p.Prime]
    (n stage : ℕ) (c : ℚ_[p]) (q0 q : Fin n → ℚ_[p])
    (x B v : Bool → ℚ_[p]) (kv : Bool → ℕ)
    (t : Finset W) (H : W → ℚ_[p][X]) (a : W → ℕ) : Prop :=
  (∀ b : Bool,
    (ShiftedEisenstein.monicFamily n c q).eval (x b) ≠ 0 ∧
    ‖(ShiftedEisenstein.monicFamily n c q).eval (x b) / B b‖ = ‖v b‖ ∧
    (v b / ((ShiftedEisenstein.monicFamily n c q).eval (x b) / B b) - 1) /
      (p : ℚ_[p]) ^ kv b ∈ PadicInt.subring p) ∧
  (∀ w ∈ t, ∀ b : Bool,
    (LocalInterpolation.wordDerivative (ShiftedEisenstein.monicFamily n c q)
      (H w) (a w) (x b)).valuation < -(stage : ℤ)) ∧
  (∀ s : ℕ, s ≤ stage → ∀ j : ℕ,
    (C c⁻¹ * (ShiftedEisenstein.monicFamily n c q -
      ShiftedEisenstein.monicFamily n c q0).comp
        (C (((p : ℚ_[p]) ^ s)⁻¹) * X)).coeff j /
          (p : ℚ_[p]) ^ stage ∈ PadicInt.subring p)

/-- The actual interpolated target gives a coefficient ball preserving both
branches, all words, and all coefficients at every scheduled scale. -/
theorem exists_local_target_tolerance {W : Type*}
    (p : ℕ) [Fact p.Prime] (n stage : ℕ) (hn : 2 < n + 1) (c : ℚ_[p])
    (x B v : Bool → ℚ_[p]) (kv : Bool → ℕ)
    (hx : ∀ b, x b ≠ 0) (hsep : x false ≠ x true)
    (hB : ∀ b, B b ≠ 0) (hv : ∀ b, v b ≠ 0)
    (t : Finset W) (H : W → ℚ_[p][X]) (a : W → ℕ)
    (hword : ∀ w ∈ t, ∀ b : Bool,
      (p : ℝ) ^ stage < ‖LocalInterpolation.wordDerivative
        (LocalInterpolation.localTarget (x false) (x true) (B false * v false)
          (B true * v true) (n + 1) c) (H w) (a w) (x b)‖) :
    let q0 : Fin n → ℚ_[p] := fun j =>
      (LocalInterpolation.localTarget (x false) (x true) (B false * v false)
        (B true * v true) (n + 1) c).coeff (j.val + 1)
    ∃ δ : ℝ, 0 < δ ∧ ∀ q : Fin n → ℚ_[p], (∀ j, ‖q j - q0 j‖ < δ) →
      ConditionsAtPrime p n stage c q0 q x B v kv t H a := by
  classical
  dsimp only
  let T := LocalInterpolation.localTarget (x false) (x true) (B false * v false)
    (B true * v true) (n + 1) c
  let q0 : Fin n → ℚ_[p] := fun j => T.coeff (j.val + 1)
  have hT : ShiftedEisenstein.monicFamily n c q0 = T :=
    localTarget_eq_monicFamily _ _ _ _ n c (hx false) (hx true) hn
  have htarget (b : Bool) : (ShiftedEisenstein.monicFamily n c q0).eval (x b) = B b * v b := by
    rw [hT]
    cases b with
    | false => exact LocalInterpolation.localTarget_eval_left _ _ _ _ _ _
    | true => exact LocalInterpolation.localTarget_eval_right _ _ _ _ _ _ hsep
  obtain ⟨δ, hδ, hstable⟩ := CoefficientStability.exists_padic_stage_tolerance_full
    n c q0 Finset.univ x B v kv (fun b _ => hB b) (fun b _ => hv b)
    (fun b _ => htarget b) (t.product Finset.univ) (fun wb => x wb.2)
    (fun wb => H wb.1) (fun wb => a wb.1) (fun _ => (p : ℝ) ^ stage)
    (fun wb hwb => by rw [hT]; exact hword wb.1 (Finset.mem_product.mp hwb).1 wb.2)
    (Finset.range (stage + 1)) (fun _ => c⁻¹) (fun s => ((p : ℚ_[p]) ^ s)⁻¹)
    (fun _ => stage)
  refine ⟨δ, hδ, ?_⟩
  intro q hq
  obtain ⟨hval, hwords, hcoeff⟩ := hstable q hq
  refine ⟨fun b => hval b (Finset.mem_univ b), ?_, ?_⟩
  · intro w hw b
    exact SignedConstant.valuation_lt_neg_of_pow_lt_norm p _ stage
      (hwords (w, b) (Finset.mem_product.mpr ⟨hw, Finset.mem_univ b⟩))
  · intro s hs j
    exact hcoeff s (Finset.mem_range.mpr (by omega)) j

/-- Both fixed polynomial families divided by c have the full scheduled
coefficient precision at every scheduled scale. -/
def ClearedAtPrime {W : Type*} (p : ℕ) [Fact p.Prime]
    (stage : ℕ) (c : ℚ_[p]) (J : ℚ_[p][X]) (t : Finset W) (H : W → ℚ_[p][X]) : Prop :=
  ∀ s : ℕ, s ≤ stage →
    (∀ k : ℕ, ((J.comp (C (((p : ℚ_[p]) ^ s)⁻¹) * X)).coeff k / c) /
      (p : ℚ_[p]) ^ stage ∈ PadicInt.subring p) ∧
    (∀ w ∈ t, ∀ k : ℕ, (((H w).comp (C (((p : ℚ_[p]) ^ s)⁻¹) * X)).coeff k / c) /
      (p : ℚ_[p]) ^ stage ∈ PadicInt.subring p)

/-- Actual finite-stage local preparation: choose the clearing exponents, then
one signed rational constant, then all coefficient balls. No local target,
clearing exponent, or approximation neighborhood is assumed to exist. -/
theorem exists_prepared_local_data {ι W : Type*} [Fintype ι]
    (p : ι → ℕ) [∀ i, Fact (p i).Prime] (hinj : Function.Injective p)
    (ell : ℕ) [Fact ell.Prime] (hfresh : ∀ i, p i ≠ ell)
    (n stage : ℕ) (hn : 2 < n + 1) (hstage : 1 ≤ stage)
    (x B v : ∀ i, Bool → ℚ_[p i]) (kv : ι → Bool → ℕ)
    (hx : ∀ i b, x i b ≠ 0) (hsep : ∀ i, x i false ≠ x i true)
    (hB : ∀ i b, B i b ≠ 0) (hv : ∀ i b, v i b ≠ 0)
    (t : Finset W) (H : ∀ i, W → ℚ_[p i][X]) (a : W → ℕ)
    (ha : ∀ w ∈ t, a w ≠ 0) (hH : ∀ i w, w ∈ t → ∀ b, (H i w).eval (x i b) ≠ 0) :
    ∃ h N : ι → ℕ, ∃ δ : ι → ℝ,
      (∀ i, ∃ e : ℕ, 0 < e ∧ N i = (ell - 1) * e) ∧
      (∀ i, 0 < N i) ∧ (∀ i, h i + stage ≤ N i) ∧
      (∀ i, 0 < δ i ∧
        ClearedAtPrime (p i) stage (SignedConstant.constant p N (n + 1))
          (LocalInterpolation.fixedRemainder (x i false) (x i true)
            (B i false * v i false) (B i true * v i true) (n + 1)) t (H i) ∧
        let q0 : Fin n → ℚ_[p i] := fun j =>
          (LocalInterpolation.localTarget (x i false) (x i true)
            (B i false * v i false) (B i true * v i true) (n + 1)
            (SignedConstant.constant p N (n + 1))).coeff (j.val + 1)
        ∀ q : Fin n → ℚ_[p i], (∀ j, ‖q j - q0 j‖ < δ i) →
          ConditionsAtPrime (p i) n stage (SignedConstant.constant p N (n + 1))
            q0 q (x i) (B i) (v i) (kv i) t (H i) a) ∧
      ∃ c : ℤ_[ell], (c : ℚ_[ell]) = (SignedConstant.constant p N (n + 1) : ℚ_[ell]) ∧
        PadicInt.toZModPow 1 c = (-1) ^ (n + 1) := by
  classical
  let J (i : ι) := LocalInterpolation.fixedRemainder (x i false) (x i true)
    (B i false * v i false) (B i true * v i true) (n + 1)
  choose h hclear using fun i => exists_clearing_for_scales (p i) stage (J i) t (H i)
  choose R hR hderiv using fun i => LocalInterpolation.exists_bound_word_derivatives
    t (x i false) (x i true) (B i false * v i false) (B i true * v i true) (n + 1)
    (hx i false) (hx i true) (hsep i) (mul_ne_zero (hB i false) (hv i false))
    (mul_ne_zero (hB i true) (hv i true)) (H i) a (fun _ => (p i : ℝ) ^ stage)
    ha (fun w hw => hH i w hw false) (fun w hw => hH i w hw true)
  obtain ⟨N, hmult, hpos, hbudget, hnorm, hc⟩ := SignedConstant.exists_constant_exponents
    p hinj ell hfresh (n + 1) stage hstage h R
  have hword (i : ι) (w : W) (hw : w ∈ t) (b : Bool) :
      (p i : ℝ) ^ stage < ‖LocalInterpolation.wordDerivative
        (LocalInterpolation.localTarget (x i false) (x i true) (B i false * v i false)
          (B i true * v i true) (n + 1) (SignedConstant.constant p N (n + 1)))
        (H i w) (a w) (x i b)‖ := by
    have hh := hderiv i _ (hnorm i) w hw
    cases b with
    | false => exact hh.1
    | true => exact hh.2
  choose δ hδ hstable using fun i => exists_local_target_tolerance
    (p i) n stage hn (SignedConstant.constant p N (n + 1))
    (x i) (B i) (v i) (kv i) (hx i) (hsep i) (hB i) (hv i) t (H i) a (hword i)
  refine ⟨h, N, δ, hmult, hpos, hbudget, fun i => ⟨hδ i, ?_, hstable i⟩, hc⟩
  intro s hs
  have hp0 : (p i : ℚ_[p i]) ^ stage ≠ 0 :=
    pow_ne_zero _ (Nat.cast_ne_zero.mpr (show (p i).Prime from Fact.out).ne_zero)
  have hintegral (z : ℚ_[p i]) (hz : ‖z‖ ≤ (p i : ℝ) ^ h i) :
      (z / (SignedConstant.constant p N (n + 1) : ℚ_[p i])) /
        (p i : ℚ_[p i]) ^ stage ∈ PadicInt.subring (p i) := by
    apply (PadicTargetStability.div_mem_padicInt_iff _ _ hp0).mpr
    rw [Padic.norm_p_pow]
    exact SignedConstant.norm_div_constant_le_stage_precision p hinj N (n + 1)
      i (h i) stage (hbudget i) z hz
  exact ⟨fun k => hintegral _ ((hclear i s hs).1 k),
    fun w hw k => hintegral _ ((hclear i s hs).2 w hw k)⟩

end UnconditionalCounterexample.LocalStageSelection
