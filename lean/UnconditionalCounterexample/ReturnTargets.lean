import UnconditionalCounterexample.LocalStageSelection
import UnconditionalCounterexample.EvaluationDVR
import UnconditionalCounterexample.PadicTargetStability
import UnconditionalCounterexample.SignedConstant
import UnconditionalCounterexample.NormalizedWords

/-!
# Concrete q-stage targets and actual return congruences

At the q_n stage of Proposition 3.1,
ordinary targets are B(gamma)*p^h. Precisely when h=0 and the previously
constructed a_n(gamma)*b_(n+1)(gamma) has norm1, use that earlier product
instead, at precision max(1,n). These choices are nonzero and have the exact
required normalized valuation. The final wrapper consumes both branches of
the actual finite selector and yields the valuation and return congruence for
the same rational normalized q=F/B and next a=A*b/q. Globalization over the
prime schedule and construction of the earlier rational functions are separate.
-/

noncomputable section
open Polynomial
namespace UnconditionalCounterexample.ReturnTargets

/-- Raw stages are one-based in the paper; q0 is the third stage. -/
theorem q_stage_one_based (n : ℕ) : (NormalizedWords.Generator.q n).stage + 1 = 2 * n + 3 := by
  simp only [NormalizedWords.Generator.stage]

/-- The actual transcendental evaluation agrees with polynomial evaluation. -/
theorem evaluationHom_polynomial (p : ℕ) [Fact p.Prime]
    (γ : ℚ_[p]) (hγ : Transcendental ℚ γ) (F : ℚ[X]) :
    EvaluationDVR.evaluationHom p γ hγ (algebraMap ℚ[X] (RatFunc ℚ) F) =
      F.eval₂ (algebraMap ℚ ℚ_[p]) γ := by
  simp [EvaluationDVR.evaluationHom, LocalEvaluation.evalAt,
    RatFunc.algEquivOfTranscendental_algebraMap, ← aeval_def]

/-- Exactly the branch where the paper refines the ordinary q-stage target. -/
def IsRefined {p : ℕ} [Fact p.Prime] (h : ℕ) (r : ℚ_[p]) : Prop := h = 0 ∧ ‖r‖ = 1

/-- Quotient target for q_n: use the earlier product on a unit branch and p^h otherwise. -/
def quotientTarget {p : ℕ} [Fact p.Prime] (h : ℕ) (r : ℚ_[p]) : ℚ_[p] := by
  classical
  exact if IsRefined h r then r else (p : ℚ_[p]) ^ h

/-- Ordinary targets use precision one; refined targets also meet precision n. -/
def precision {p : ℕ} [Fact p.Prime] (n h : ℕ) (r : ℚ_[p]) : ℕ := by
  classical
  exact if IsRefined h r then max 1 n else 1

theorem quotientTarget_norm {p : ℕ} [Fact p.Prime] (h : ℕ) (r : ℚ_[p]) :
    ‖quotientTarget h r‖ = (p : ℝ) ^ (-(h : ℤ)) := by
  classical
  unfold quotientTarget
  split_ifs with hr
  · rw [hr.1, hr.2]
    simp
  · exact Padic.norm_p_pow h

theorem quotientTarget_ne_zero {p : ℕ} [Fact p.Prime] (h : ℕ) (r : ℚ_[p]) :
    quotientTarget h r ≠ 0 := by
  apply norm_pos_iff.mp
  rw [quotientTarget_norm]
  exact zpow_pos (Nat.cast_pos.mpr (show p.Prime from Fact.out).pos) _

theorem precision_pos {p : ℕ} [Fact p.Prime] (n h : ℕ) (r : ℚ_[p]) :
    0 < precision n h r := by
  classical
  unfold precision
  split_ifs <;> omega

theorem refined_quotientTarget {p : ℕ} [Fact p.Prime] (h : ℕ) (r : ℚ_[p])
    (href : IsRefined h r) : quotientTarget h r = r := by
  simp only [quotientTarget, href, ite_true]

theorem refined_precision_ge {p : ℕ} [Fact p.Prime] (n h : ℕ) (r : ℚ_[p])
    (href : IsRefined h r) : n ≤ precision n h r := by
  simp only [precision, href, ite_true]
  exact le_max_right _ _

/-- Weakening a local return precision preserves actual p-adic integrality. -/
theorem div_prime_pow_mem_of_le {p : ℕ} [Fact p.Prime]
    (e : ℚ_[p]) (n m : ℕ) (hnm : n ≤ m)
    (he : e / (p : ℚ_[p]) ^ m ∈ PadicInt.subring p) :
    e / (p : ℚ_[p]) ^ n ∈ PadicInt.subring p := by
  have hp0 : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr (show p.Prime from Fact.out).ne_zero
  apply (PadicTargetStability.div_mem_padicInt_iff _ _ (pow_ne_zero _ hp0)).mpr
  have hb := (PadicTargetStability.div_mem_padicInt_iff _ _ (pow_ne_zero _ hp0)).mp he
  apply hb.trans
  rw [Padic.norm_p_pow, Padic.norm_p_pow]
  apply zpow_le_zpow_right₀
  · exact_mod_cast (show p.Prime from Fact.out).one_le
  · omega

/-- Every monic earlier denominator has a nonzero actual evaluation. This also
covers B1=1 without a special case. -/
theorem polynomial_eval_ne_zero (p : ℕ) [Fact p.Prime]
    (γ : ℚ_[p]) (hγ : Transcendental ℚ γ) (B : ℚ[X]) (hB : B.Monic) :
    B.eval₂ (algebraMap ℚ ℚ_[p]) γ ≠ 0 := by
  rw [← evaluationHom_polynomial p γ hγ B]
  have hB0 : algebraMap ℚ[X] (RatFunc ℚ) B ≠ 0 := by
    simpa only [map_zero] using (RatFunc.algebraMap_injective ℚ).ne hB.ne_zero
  simpa only [map_zero] using (EvaluationDVR.evaluationHom p γ hγ).injective.ne hB0

/-- A selected normalized q-value has precisely the required additive valuation. -/
theorem valuation_of_target_norm {p : ℕ} [Fact p.Prime]
    (h : ℕ) (r z : ℚ_[p]) (hz : ‖z‖ = ‖quotientTarget h r‖) : z.valuation = h := by
  have hz0 : z ≠ 0 := norm_pos_iff.mp (hz.symm ▸ norm_pos_iff.mpr (quotientTarget_ne_zero h r))
  rw [Padic.norm_eq_zpow_neg_valuation hz0, quotientTarget_norm] at hz
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (show p.Prime from Fact.out).one_lt
  have he := zpow_right_injective₀ (zero_lt_one.trans hp1) (ne_of_gt hp1) hz
  omega

/-- The recurrence is an actual rational-function identity. -/
def nextReturn (A b q : RatFunc ℚ) : RatFunc ℚ := A * b / q

/-- Concrete ordinary/refined q-stage target, using the previously defined
rational functions a_n and b_(n+1) rather than a free local scalar. -/
def targetFromPrevious (p : ℕ) [Fact p.Prime]
    (γ : ℚ_[p]) (hγ : Transcendental ℚ γ) (A b : RatFunc ℚ) (h : ℕ) : ℚ_[p] :=
  quotientTarget h (EvaluationDVR.evaluationHom p γ hγ (A * b))

/-- The actual numerator target used by two-point interpolation. -/
def numeratorTarget (p : ℕ) [Fact p.Prime]
    (γ : ℚ_[p]) (hγ : Transcendental ℚ γ) (B : ℚ[X]) (A b : RatFunc ℚ) (h : ℕ) : ℚ_[p] :=
  B.eval₂ (algebraMap ℚ ℚ_[p]) γ * targetFromPrevious p γ hγ A b h

theorem numeratorTarget_ne_zero (p : ℕ) [Fact p.Prime]
    (γ : ℚ_[p]) (hγ : Transcendental ℚ γ) (B : ℚ[X]) (hB : B.Monic)
    (A b : RatFunc ℚ) (h : ℕ) : numeratorTarget p γ hγ B A b h ≠ 0 :=
  mul_ne_zero (polynomial_eval_ne_zero p γ hγ B hB) (quotientTarget_ne_zero _ _)

/-- The selected raw quotient evaluates by the same numerator/denominator pair
used by finite-stage interpolation. -/
theorem evaluation_normalized_polynomial (p : ℕ) [Fact p.Prime]
    (γ : ℚ_[p]) (hγ : Transcendental ℚ γ) (F B : ℚ[X]) :
    EvaluationDVR.evaluationHom p γ hγ
      (algebraMap ℚ[X] (RatFunc ℚ) F / algebraMap ℚ[X] (RatFunc ℚ) B) =
      F.eval₂ (algebraMap ℚ ℚ_[p]) γ / B.eval₂ (algebraMap ℚ ℚ_[p]) γ := by
  rw [map_div₀, evaluationHom_polynomial, evaluationHom_polynomial]

/-- Evaluation of the actual next return element is the local quotient tested
by ConditionsAtPrime. -/
theorem evaluation_nextReturn (p : ℕ) [Fact p.Prime]
    (γ : ℚ_[p]) (hγ : Transcendental ℚ γ) (A b : RatFunc ℚ) (F B : ℚ[X]) :
    EvaluationDVR.evaluationHom p γ hγ
      (nextReturn A b (algebraMap ℚ[X] (RatFunc ℚ) F / algebraMap ℚ[X] (RatFunc ℚ) B)) =
      EvaluationDVR.evaluationHom p γ hγ (A * b) /
        (F.eval₂ (algebraMap ℚ ℚ_[p]) γ / B.eval₂ (algebraMap ℚ ℚ_[p]) γ) := by
  rw [nextReturn, map_div₀, evaluation_normalized_polynomial]

/-- On every refined branch the finite selector's return condition implies
precision n for the actual rational recurrence a_(n+1)=a_n*b_(n+1)/q_n. -/
theorem actual_refined_return (p : ℕ) [Fact p.Prime]
    (γ : ℚ_[p]) (hγ : Transcendental ℚ γ) (A b : RatFunc ℚ) (F B : ℚ[X])
    (n h : ℕ)
    (href : IsRefined h (EvaluationDVR.evaluationHom p γ hγ (A * b)))
    (hreturn :
      (targetFromPrevious p γ hγ A b h /
        (F.eval₂ (algebraMap ℚ ℚ_[p]) γ / B.eval₂ (algebraMap ℚ ℚ_[p]) γ) - 1) /
        (p : ℚ_[p]) ^ precision n h (EvaluationDVR.evaluationHom p γ hγ (A * b)) ∈
          PadicInt.subring p) :
    (EvaluationDVR.evaluationHom p γ hγ
      (nextReturn A b (algebraMap ℚ[X] (RatFunc ℚ) F / algebraMap ℚ[X] (RatFunc ℚ) B)) - 1) /
        (p : ℚ_[p]) ^ n ∈ PadicInt.subring p := by
  rw [evaluation_nextReturn]
  apply div_prime_pow_mem_of_le _ n _ (refined_precision_ge n h _ href)
  simpa only [targetFromPrevious, refined_quotientTarget h _ href] using hreturn

/-- The finite selector's quotient norm conclusion gives the actual required
valuation of the newly selected normalized rational function. -/
theorem actual_normalized_valuation (p : ℕ) [Fact p.Prime]
    (γ : ℚ_[p]) (hγ : Transcendental ℚ γ) (A b : RatFunc ℚ) (F B : ℚ[X]) (h : ℕ)
    (hnorm : ‖F.eval₂ (algebraMap ℚ ℚ_[p]) γ / B.eval₂ (algebraMap ℚ ℚ_[p]) γ‖ =
      ‖targetFromPrevious p γ hγ A b h‖) :
    (EvaluationDVR.evaluationHom p γ hγ
      (algebraMap ℚ[X] (RatFunc ℚ) F / algebraMap ℚ[X] (RatFunc ℚ) B)).valuation = h := by
  rw [evaluation_normalized_polynomial]
  exact valuation_of_target_norm h _ _ hnorm

/-- A unit relative quotient has the same precision in either direction. This
recovers the paper's forward relative congruence from the selector's return form. -/
theorem forward_relative_integral_of_return {p : ℕ} [Fact p.Prime]
    (z v : ℚ_[p]) (hv : v ≠ 0) (hnorm : ‖z‖ = ‖v‖) (k : ℕ)
    (hret : (v / z - 1) / (p : ℚ_[p]) ^ k ∈ PadicInt.subring p) :
    (z / v - 1) / (p : ℚ_[p]) ^ k ∈ PadicInt.subring p := by
  have hz : z ≠ 0 := norm_pos_iff.mp (hnorm.symm ▸ norm_pos_iff.mpr hv)
  have hid : z / v - 1 = -(z / v) * (v / z - 1) := by
    field_simp
    ring
  have heq : ‖z / v - 1‖ = ‖v / z - 1‖ := by
    rw [hid, norm_mul, norm_neg, norm_div, hnorm,
      div_self (norm_ne_zero_iff.mpr hv), one_mul]
  have hp0 := pow_ne_zero k (Nat.cast_ne_zero.mpr (show p.Prime from Fact.out).ne_zero : (p : ℚ_[p]) ≠ 0)
  rw [PadicTargetStability.div_mem_padicInt_iff _ _ hp0, heq]
  exact (PadicTargetStability.div_mem_padicInt_iff _ _ hp0).mp hret

/-- Ordinary and refined actual numerator targets satisfy the exact relative
congruence F(γ)/η−1∈p^k Z_p required in the current construction. -/
theorem actual_relative_target (p : ℕ) [Fact p.Prime]
    (γ : ℚ_[p]) (hγ : Transcendental ℚ γ) (A b : RatFunc ℚ) (F B : ℚ[X]) (n h : ℕ)
    (hnorm : ‖F.eval₂ (algebraMap ℚ ℚ_[p]) γ / B.eval₂ (algebraMap ℚ ℚ_[p]) γ‖ =
      ‖targetFromPrevious p γ hγ A b h‖)
    (hreturn :
      (targetFromPrevious p γ hγ A b h /
        (F.eval₂ (algebraMap ℚ ℚ_[p]) γ / B.eval₂ (algebraMap ℚ ℚ_[p]) γ) - 1) /
        (p : ℚ_[p]) ^ precision n h (EvaluationDVR.evaluationHom p γ hγ (A * b)) ∈
          PadicInt.subring p) :
    (F.eval₂ (algebraMap ℚ ℚ_[p]) γ / numeratorTarget p γ hγ B A b h - 1) /
      (p : ℚ_[p]) ^ precision n h (EvaluationDVR.evaluationHom p γ hγ (A * b)) ∈
        PadicInt.subring p := by
  have hforward := forward_relative_integral_of_return _ (targetFromPrevious p γ hγ A b h)
    (quotientTarget_ne_zero _ _) hnorm _ hreturn
  simpa only [numeratorTarget, div_div] using hforward

end UnconditionalCounterexample.ReturnTargets

namespace UnconditionalCounterexample.ReturnTargets

/-- The two-branch finite-selector output applies directly to the actual next
normalized q and its actual rational return recurrence. -/
theorem conditionsAtPrime_actual_q {W : Type*} (p : ℕ) [Fact p.Prime]
    (n stage returnIndex : ℕ) (c : ℚ) (q0 : Fin n → ℚ_[p]) (q : Fin n → ℚ)
    (x : Bool → ℚ_[p]) (hx : ∀ b, Transcendental ℚ (x b))
    (A b : RatFunc ℚ) (B : ℚ[X]) (h : Bool → ℕ)
    (t : Finset W) (H : W → ℚ_[p][X]) (a : W → ℕ)
    (hc : LocalStageSelection.ConditionsAtPrime p n stage (c : ℚ_[p]) q0
      (fun j => (q j : ℚ_[p])) x
      (fun β => B.eval₂ (algebraMap ℚ ℚ_[p]) (x β))
      (fun β => targetFromPrevious p (x β) (hx β) A b (h β))
      (fun β => precision returnIndex (h β) (EvaluationDVR.evaluationHom p (x β) (hx β) (A * b)))
      t H a) :
    let F := ShiftedEisenstein.monicFamily n c q
    let Q := algebraMap ℚ[X] (RatFunc ℚ) F / algebraMap ℚ[X] (RatFunc ℚ) B
    ∀ β : Bool,
      (EvaluationDVR.evaluationHom p (x β) (hx β) Q).valuation = h β ∧
      (IsRefined (h β) (EvaluationDVR.evaluationHom p (x β) (hx β) (A * b)) →
        (EvaluationDVR.evaluationHom p (x β) (hx β) (nextReturn A b Q) - 1) /
          (p : ℚ_[p]) ^ returnIndex ∈ PadicInt.subring p) := by
  dsimp only
  intro β
  have heval :
      (ShiftedEisenstein.monicFamily n (c : ℚ_[p]) (fun j => (q j : ℚ_[p]))).eval (x β) =
      (ShiftedEisenstein.monicFamily n c q).eval₂ (algebraMap ℚ ℚ_[p]) (x β) := by
    have hmap := ShiftedEisenstein.monicFamily_map (algebraMap ℚ ℚ_[p]) n c q
    have hcast (r : ℚ) : algebraMap ℚ ℚ_[p] r = (r : ℚ_[p]) := by
      simpa only [Rat.cast_id] using map_ratCast (algebraMap ℚ ℚ_[p]) r
    simp only [hcast] at hmap
    rw [← hmap, Polynomial.eval_map]
  have hnorm := (hc.1 β).2.1
  have hreturn := (hc.1 β).2.2
  rw [heval] at hnorm hreturn
  refine ⟨actual_normalized_valuation p (x β) (hx β) A b _ B (h β) hnorm, ?_⟩
  intro href
  exact actual_refined_return p (x β) (hx β) A b _ B returnIndex (h β) href hreturn

end UnconditionalCounterexample.ReturnTargets