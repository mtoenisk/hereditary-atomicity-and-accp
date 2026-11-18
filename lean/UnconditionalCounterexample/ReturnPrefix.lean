import UnconditionalCounterexample.ReturnTargets
import UnconditionalCounterexample.RecursivePrefix
import UnconditionalCounterexample.ConstructionWords
import UnconditionalCounterexample.ScheduledRecovery

/-!
# Actual return data from the stored raw prefix

The canonical b/q selectors use the construction's interleaved raw stages.
The a sequence is the literal rational recurrence starting at X. Its finite
prefix dependence, exact persistence under append, and the new normalized
quotient formula link the same stored F/E data to the finite local selector.
No global primary profiles or eventual return conclusion is assumed here.
-/

noncomputable section
namespace UnconditionalCounterexample.ReturnPrefix
open Polynomial NormalizedWords

/-- The normalized b_n in the raw construction order. -/
def b (U : ℕ → RatFunc ℚ) (n : ℕ) : RatFunc ℚ := U (Generator.b n).stage

/-- The normalized q_n in the raw construction order. -/
def q (U : ℕ → RatFunc ℚ) (n : ℕ) : RatFunc ℚ := U (Generator.q n).stage

/-- The actual return sequence, beginning at the rational function t. -/
def a (U : ℕ → RatFunc ℚ) : ℕ → RatFunc ℚ
  | 0 => RatFunc.X
  | n + 1 => a U n * b U (n + 1) / q U n

@[simp] theorem a_zero (U : ℕ → RatFunc ℚ) : a U 0 = RatFunc.X := rfl
@[simp] theorem a_succ (U : ℕ → RatFunc ℚ) (n : ℕ) :
    a U (n + 1) = a U n * b U (n + 1) / q U n := rfl

@[simp] theorem b_succ (U : ℕ → RatFunc ℚ) (n : ℕ) : b U (n + 1) = U (2 * n + 1) := rfl
@[simp] theorem q_eq (U : ℕ → RatFunc ℚ) (n : ℕ) : q U n = U (2 * n + 2) := rfl

theorem b_ne_zero (U : ℕ → RatFunc ℚ) (hU : ∀ j, U j ≠ 0) (n : ℕ) : b U n ≠ 0 := hU _
theorem q_ne_zero (U : ℕ → RatFunc ℚ) (hU : ∀ j, U j ≠ 0) (n : ℕ) : q U n ≠ 0 := hU _
theorem a_ne_zero (U : ℕ → RatFunc ℚ) (hU : ∀ j, U j ≠ 0) (n : ℕ) : a U n ≠ 0 := by
  induction n with
  | zero => exact RatFunc.X_ne_zero
  | succ n ih => exact div_ne_zero (mul_ne_zero ih (b_ne_zero U hU _)) (q_ne_zero U hU _)

/-- a_n uses no normalized generator later than the previous q stage. -/
theorem a_congr (U V : ℕ → RatFunc ℚ) (n : ℕ)
    (hUV : ∀ j < 2 * n + 1, U j = V j) : a U n = a V n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [a_succ, a_succ, ih (fun j hj => hUV j (by omega)), b_succ, b_succ, q_eq, q_eq,
      hUV (2 * n + 1) (by omega), hUV (2 * n + 2) (by omega)]

/-- Every factor and its denominator depend only on the preceding raw prefix. -/
theorem generators_congr (F G : ℕ → ℚ[X]) (E D : ℕ → ℕ) (j : ℕ)
    (hF : ∀ k ≤ j, F k = G k) (hE : E j = D j) :
    ScheduledRecovery.generators F E j = ScheduledRecovery.generators G D j := by
  unfold ScheduledRecovery.generators RawWords.normalizedFactor
  dsimp only
  rw [hF j le_rfl, hE]
  congr 1
  apply Finset.prod_congr rfl
  intro k hk
  rw [hF k (Nat.le_of_lt (Finset.mem_range.mp hk))]

theorem generators_ne_zero (F : ℕ → ℚ[X]) (E : ℕ → ℕ) (hF : ∀ j, F j ≠ 0) (j : ℕ) :
    ScheduledRecovery.generators F E j ≠ 0 := by
  apply div_ne_zero
  · exact (map_ne_zero_iff (algebraMap ℚ[X] (RatFunc ℚ)) (RatFunc.algebraMap_injective ℚ)).mpr (hF j)
  · apply Finset.prod_ne_zero_iff.mpr
    intro k hk
    exact pow_ne_zero _ ((map_ne_zero_iff (algebraMap ℚ[X] (RatFunc ℚ))
      (RatFunc.algebraMap_injective ℚ)).mpr (hF k))

end UnconditionalCounterexample.ReturnPrefix

namespace UnconditionalCounterexample.RecursivePrefix.Prefix
open Polynomial
variable {m : ℕ} (P : RecursivePrefix.Prefix m)

def generators : ℕ → RatFunc ℚ := ScheduledRecovery.generators P.rawAt P.exponentAt

def a (n : ℕ) : RatFunc ℚ := ReturnPrefix.a P.generators n

def b (n : ℕ) : RatFunc ℚ := ReturnPrefix.b P.generators n

def q (n : ℕ) : RatFunc ℚ := ReturnPrefix.q P.generators n

theorem rawAt_ne_zero (j : ℕ) : P.rawAt j ≠ 0 := by
  unfold RecursivePrefix.Prefix.rawAt
  split_ifs with hj
  · exact (P.monic _).ne_zero
  · exact one_ne_zero

theorem generators_ne_zero (j : ℕ) : P.generators j ≠ 0 :=
  ReturnPrefix.generators_ne_zero _ _ P.rawAt_ne_zero j

theorem a_ne_zero (n : ℕ) : P.a n ≠ 0 := ReturnPrefix.a_ne_zero _ P.generators_ne_zero n

theorem b_ne_zero (n : ℕ) : P.b n ≠ 0 := ReturnPrefix.b_ne_zero _ P.generators_ne_zero n

theorem q_ne_zero (n : ℕ) : P.q n ≠ 0 := ReturnPrefix.q_ne_zero _ P.generators_ne_zero n

/-- Actual q-stage local target using exactly the already stored prefix. -/
def qTarget (n : ℕ) (p : ℕ) [Fact p.Prime] (γ : ℚ_[p])
    (hγ : Transcendental ℚ γ) (h : ℕ) : ℚ_[p] :=
  ReturnTargets.targetFromPrevious p γ hγ (P.a n) (P.b (n + 1)) h

def qPrecision (n : ℕ) (p : ℕ) [Fact p.Prime] (γ : ℚ_[p])
    (hγ : Transcendental ℚ γ) (h : ℕ) : ℕ :=
  ReturnTargets.precision n h (EvaluationDVR.evaluationHom p γ hγ (P.a n * P.b (n + 1)))

theorem qTarget_ne_zero (n : ℕ) (p : ℕ) [Fact p.Prime] (γ : ℚ_[p])
    (hγ : Transcendental ℚ γ) (h : ℕ) : P.qTarget n p γ hγ h ≠ 0 :=
  ReturnTargets.quotientTarget_ne_zero _ _

end UnconditionalCounterexample.RecursivePrefix.Prefix

namespace UnconditionalCounterexample.RecursivePrefix.Next
open Polynomial
variable {m : ℕ} {P : Prefix m} (S : Next P)

theorem generators_old (j : ℕ) (hj : j < m) : S.append.generators j = P.generators j := by
  apply ReturnPrefix.generators_congr
  · intro k hk
    have hkm : k < m := lt_of_le_of_lt hk hj
    rw [S.append.rawAt_lt k (by omega), P.rawAt_lt k hkm]
    exact S.append_raw_old ⟨k, hkm⟩
  · rw [S.append.exponentAt_lt j (by omega), P.exponentAt_lt j hj]
    exact S.append_exponent_old ⟨j, hj⟩

theorem a_old (n : ℕ) (hn : 2 * n + 1 ≤ m) : S.append.a n = P.a n := by
  apply ReturnPrefix.a_congr
  intro j hj
  exact S.generators_old j (lt_of_lt_of_le hj hn)

theorem b_succ_old (n : ℕ) (hn : 2 * n + 1 < m) : S.append.b (n + 1) = P.b (n + 1) :=
  S.generators_old _ hn

/-- The new normalized generator uses the actual stored new raw and exponent. -/
theorem generators_last :
    S.append.generators m = algebraMap ℚ[X] (RatFunc ℚ) S.raw /
      algebraMap ℚ[X] (RatFunc ℚ) (∏ j : Fin m, P.rawAt j ^ S.exponent) := by
  unfold Prefix.generators ScheduledRecovery.generators RawWords.normalizedFactor
  dsimp only
  have hr : S.append.rawAt m = S.raw := by
    rw [S.append.rawAt_lt m (by omega)]
    exact (congrArg S.append.raw (Fin.ext rfl)).trans S.append_raw_last
  have he : S.append.exponentAt m = S.exponent := by
    rw [S.append.exponentAt_lt m (by omega)]
    exact (congrArg S.append.exponent (Fin.ext rfl)).trans S.append_exponent_last
  rw [hr, he]
  change algebraMap ℚ[X] (RatFunc ℚ) S.raw /
    (∏ j ∈ Finset.range m, algebraMap ℚ[X] (RatFunc ℚ) (S.append.rawAt j) ^ S.exponent) = _
  congr 1
  rw [Fin.prod_univ_eq_prod_range (fun j => P.rawAt j ^ S.exponent) m, map_prod]
  apply Finset.prod_congr rfl
  intro j hj
  have hjm := Finset.mem_range.mp hj
  rw [map_pow, S.append.rawAt_lt j (by omega), P.rawAt_lt j hjm]
  exact congrArg (fun Z : ℚ[X] => algebraMap ℚ[X] (RatFunc ℚ) Z ^ S.exponent)
    (S.append_raw_old ⟨j, hjm⟩)

/-- Appending q_n realizes the same recurrence as the local return target. -/
theorem a_succ_at_q {n : ℕ} {P : Prefix (2 * n + 2)} (S : Next P) :
    S.append.a (n + 1) = ReturnTargets.nextReturn (P.a n) (P.b (n + 1))
      (algebraMap ℚ[X] (RatFunc ℚ) S.raw /
        algebraMap ℚ[X] (RatFunc ℚ) (∏ j : Fin (2 * n + 2), P.rawAt j ^ S.exponent)) := by
  change ReturnPrefix.a S.append.generators (n + 1) = _
  rw [ReturnPrefix.a_succ]
  change S.append.a n * S.append.b (n + 1) / S.append.q n = _
  rw [S.a_old n (by omega), S.b_succ_old n (by omega)]
  change P.a n * P.b (n + 1) / S.append.generators (2 * n + 2) = _
  rw [S.generators_last]
  rfl

end UnconditionalCounterexample.RecursivePrefix.Next

namespace UnconditionalCounterexample.RecursivePrefix.Prefix
open NormalizedWords Polynomial
variable {m : ℕ} (P : RecursivePrefix.Prefix m)

/-- All b-stages use the ordinary target; q-stages use the concrete return target. -/
def generatorTarget (g : Generator) (p : ℕ) [Fact p.Prime] (γ : ℚ_[p])
    (hγ : Transcendental ℚ γ) (h : ℕ) : ℚ_[p] :=
  match g with
  | .b _ => (p : ℚ_[p]) ^ h
  | .q n => P.qTarget n p γ hγ h

def generatorPrecision (g : Generator) (p : ℕ) [Fact p.Prime] (γ : ℚ_[p])
    (hγ : Transcendental ℚ γ) (h : ℕ) : ℕ :=
  match g with
  | .b _ => 1
  | .q n => P.qPrecision n p γ hγ h

theorem generatorTarget_ne_zero (g : Generator) (p : ℕ) [Fact p.Prime] (γ : ℚ_[p])
    (hγ : Transcendental ℚ γ) (h : ℕ) : P.generatorTarget g p γ hγ h ≠ 0 := by
  cases g with
  | b n => exact pow_ne_zero _ (Nat.cast_ne_zero.mpr (show p.Prime from Fact.out).ne_zero)
  | q n => exact P.qTarget_ne_zero n p γ hγ h

theorem generatorTarget_norm (g : Generator) (p : ℕ) [Fact p.Prime] (γ : ℚ_[p])
    (hγ : Transcendental ℚ γ) (h : ℕ) :
    ‖P.generatorTarget g p γ hγ h‖ = (p : ℝ) ^ (-(h : ℤ)) := by
  cases g with
  | b n => exact Padic.norm_p_pow h
  | q n => exact ReturnTargets.quotientTarget_norm _ _

theorem generatorPrecision_pos (g : Generator) (p : ℕ) [Fact p.Prime] (γ : ℚ_[p])
    (hγ : Transcendental ℚ γ) (h : ℕ) : 0 < P.generatorPrecision g p γ hγ h := by
  cases g with
  | b n => exact Nat.zero_lt_one
  | q n => exact ReturnTargets.precision_pos _ _ _

end UnconditionalCounterexample.RecursivePrefix.Prefix

namespace UnconditionalCounterexample.ReturnPrefix
open Polynomial ConstructionWords

/-- A selected q-stage Choice has the required valuation and actual next-return
congruence after it is appended to the same prefix with its chosen normalization.
The equalities link the structural append to the literal selected polynomial. -/
theorem choice_q_actual {ι : Type*} [Fintype ι]
    (p : ι → ℕ) [∀ i, Fact (p i).Prime] (ell : ℕ) [Fact ell.Prime]
    (n : ℕ) (P : RecursivePrefix.Prefix (2 * n + 2))
    (plan : DegreePlan (2 * n + 2) P.rawAt P.exponentAt)
    (x : ∀ i, Bool → ℚ_[p i]) (hx : ∀ i b, Transcendental ℚ (x i b))
    (h : ι → Bool → ℕ)
    (choice : Choice p ell plan x
      (fun i b => P.qTarget n (p i) (x i b) (hx i b) (h i b))
      (fun i b => P.qPrecision n (p i) (x i b) (hx i b) (h i b)))
    (S : RecursivePrefix.Next P)
    (hraw : S.raw = ShiftedEisenstein.monicFamily (plan.degree - 1)
      (SignedConstant.constant p choice.N (plan.degree - 1 + 1)) choice.coeff)
    (hE : S.exponent = plan.E) :
    ∀ i b,
      (EvaluationDVR.evaluationHom (p i) (x i b) (hx i b) (S.append.q n)).valuation = h i b ∧
      (ReturnTargets.IsRefined (h i b)
        (EvaluationDVR.evaluationHom (p i) (x i b) (hx i b) (P.a n * P.b (n + 1))) →
        (EvaluationDVR.evaluationHom (p i) (x i b) (hx i b) (S.append.a (n + 1)) - 1) /
          (p i : ℚ_[p i]) ^ n ∈ PadicInt.subring (p i)) := by
  intro i β
  let c := SignedConstant.constant p choice.N (plan.degree - 1 + 1)
  let F := ShiftedEisenstein.monicFamily (plan.degree - 1) c choice.coeff
  have hQ : S.append.q n = algebraMap ℚ[X] (RatFunc ℚ) F /
      algebraMap ℚ[X] (RatFunc ℚ) plan.rawDen := by
    change S.append.generators (2 * n + 2) = _
    rw [S.generators_last, hraw, hE]
    rfl
  have hA : S.append.a (n + 1) = ReturnTargets.nextReturn (P.a n) (P.b (n + 1))
      (algebraMap ℚ[X] (RatFunc ℚ) F / algebraMap ℚ[X] (RatFunc ℚ) plan.rawDen) := by
    rw [S.a_succ_at_q, hraw, hE]
    rfl
  have hc := (choice.witnesses.2.2.2.2.2.1 i).2
  have hout := ReturnTargets.conditionsAtPrime_actual_q (p i) (plan.degree - 1)
    (2 * n + 2 + 1) n c _ choice.coeff (x i) (hx i) (P.a n) (P.b (n + 1))
    plan.rawDen (h i) Finset.univ
    (fun w => (plan.wordDen w).map (algebraMap ℚ ℚ_[p i]))
    RawWords.StageWord.latestExponent hc β
  rw [hQ, hA]
  exact hout

end UnconditionalCounterexample.ReturnPrefix

namespace UnconditionalCounterexample.ReturnPrefix
open Polynomial ConstructionWords

/-- Every selected stage has the actual normalized norm prescribed by its local
target, after appending precisely the same selected raw polynomial and power. -/
theorem choice_actual_norm {ι : Type*} [Fintype ι]
    (p : ι → ℕ) [∀ i, Fact (p i).Prime] (ell : ℕ) [Fact ell.Prime]
    (m : ℕ) (P : RecursivePrefix.Prefix m)
    (plan : DegreePlan m P.rawAt P.exponentAt)
    (x v : ∀ i, Bool → ℚ_[p i]) (hx : ∀ i b, Transcendental ℚ (x i b))
    (kv : ι → Bool → ℕ) (choice : Choice p ell plan x v kv)
    (S : RecursivePrefix.Next P)
    (hraw : S.raw = ShiftedEisenstein.monicFamily (plan.degree - 1)
      (SignedConstant.constant p choice.N (plan.degree - 1 + 1)) choice.coeff)
    (hE : S.exponent = plan.E) :
    ∀ i b, ‖EvaluationDVR.evaluationHom (p i) (x i b) (hx i b) (S.append.generators m)‖ = ‖v i b‖ := by
  intro i β
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
  have hn := (((choice.witnesses.2.2.2.2.2.1 i).2).1 β).2.1
  change ‖(ShiftedEisenstein.monicFamily (plan.degree - 1) (c : ℚ_[p i])
    (fun j => (choice.coeff j : ℚ_[p i]))).eval (x i β) /
      plan.rawDen.eval₂ (algebraMap ℚ ℚ_[p i]) (x i β)‖ = ‖v i β‖ at hn
  rw [← hmap, Polynomial.eval_map] at hn
  rw [hQ, ReturnTargets.evaluation_normalized_polynomial]
  exact hn

/-- Both ordinary b-stages and refined q-stages have the exact desired actual
primary/guard orders, for the same appended normalized generator. -/
theorem choice_generator_values {ι : Type*} [Fintype ι]
    (p : ι → ℕ) [∀ i, Fact (p i).Prime] (ell : ℕ) [Fact ell.Prime]
    (m : ℕ) (P : RecursivePrefix.Prefix m)
    (plan : DegreePlan m P.rawAt P.exponentAt) (g : NormalizedWords.Generator)
    (x : ∀ i, Bool → ℚ_[p i]) (hx : ∀ i b, Transcendental ℚ (x i b))
    (h : ι → Bool → ℕ)
    (choice : Choice p ell plan x
      (fun i b => P.generatorTarget g (p i) (x i b) (hx i b) (h i b))
      (fun i b => P.generatorPrecision g (p i) (x i b) (hx i b) (h i b)))
    (S : RecursivePrefix.Next P)
    (hraw : S.raw = ShiftedEisenstein.monicFamily (plan.degree - 1)
      (SignedConstant.constant p choice.N (plan.degree - 1 + 1)) choice.coeff)
    (hE : S.exponent = plan.E) :
    ∀ i b, (EvaluationDVR.evaluationHom (p i) (x i b) (hx i b)
      (S.append.generators m)).valuation = h i b := by
  have hn := choice_actual_norm p ell m P plan x _ hx _ choice S hraw hE
  intro i β
  apply ReturnTargets.valuation_of_target_norm (h i β) (0 : ℚ_[p i]) _
  rw [hn i β, P.generatorTarget_norm, ReturnTargets.quotientTarget_norm]

end UnconditionalCounterexample.ReturnPrefix
