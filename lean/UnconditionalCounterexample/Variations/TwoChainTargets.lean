import UnconditionalCounterexample.MixedReturnPrefix
import UnconditionalCounterexample.Variations.TwoChainSchedule
import UnconditionalCounterexample.Variations.TwoChainSeeds

/-!
# Local targets for both moving-atom families

Each step introduces exactly one new primary. A b-step first uses its even
coordinate; a q-step first uses its odd coordinate. Thus the permanent birth
stage of a primary identifies its colour and coordinate. The q-target for a
given colour is evaluated from its own seed and the earlier raws of the
same coherent prefix.
-/

noncomputable section
namespace UnconditionalCounterexample.TwoChains

open NormalizedWords RecursivePrefix CombinedGuardStep
open Variations.TwoChainSchedule Variations.Univariate

/-- Primary coordinate appearing for the first time when a generator is chosen. -/
def newIndex : Generator → ℕ
  | .b n => 2*n
  | .q n => 2*n+1

/-- The prescribed order is two at each exceptional initial primary, one elsewhere. -/
def displacementOrder (birth : ℕ) : ℕ :=
  if newIndex (decode birth).2 = 0 then 2 else 1

theorem displacementOrder_pos (birth : ℕ) : 0 < displacementOrder birth := by
  unfold displacementOrder
  split <;> decide

/-- Additive value prescribed at a branch of the selected prime. -/
def requestedOrder (raw birth : ℕ) (branch : Bool) : ℕ :=
  if branch then 0 else (weight raw (decode birth).1 (newIndex (decode birth).2)).toNat

/-- A primary born later has zero order on this raw, the condition supplied by
screening old raws at both local arguments of every birth prime. -/
theorem weight_zero_before_birth (raw birth : ℕ) (h : raw < birth) :
    weight raw (decode birth).1 (newIndex (decode birth).2) = 0 := by
  obtain ⟨c, g, rfl⟩ := stage_surjective birth
  simp only [decode_stage]
  cases g with
  | b n =>
    cases n with
    | zero =>
      simp only [newIndex, Nat.mul_zero, weight]
      have h₁ : raw ≠ stage c (.b 0) := Nat.ne_of_lt h
      have h₂ : raw ≠ stage c (.q 0) := Nat.ne_of_lt
        (h.trans (stage_lt_of_lt c (show (Generator.b 0).stage < (Generator.q 0).stage by decide)))
      simp [h₁, h₂]
    | succ n =>
      simp only [newIndex, Nat.mul_add, Nat.mul_one, weight_even]
      have h₁ : raw ≠ stage c (.b (n+1)) := Nat.ne_of_lt h
      have h₂ : raw ≠ stage c (.q (n+1)) := Nat.ne_of_lt
        (h.trans (stage_lt_of_lt c (by simp [Generator.stage])))
      have h₃ : raw ≠ stage c (.q n) := Nat.ne_of_lt
        (h.trans (stage_lt_of_lt c (by simp [Generator.stage])))
      simp [h₁, h₂, h₃]
  | q n => simp [newIndex, Nat.ne_of_lt h]

/-- Moving elements on either colour use the same infinite generator list. -/
def moving (U : ℕ → RatFunc ℚ) (c : Bool) : ℕ → RatFunc ℚ
  | 0 => seed c
  | n+1 => moving U c n * U (stage c (.b (n+1))) / U (stage c (.q n))

theorem moving_ne_zero (U : ℕ → RatFunc ℚ) (hu : ∀ j, U j ≠ 0) (c : Bool) (n : ℕ) :
    moving U c n ≠ 0 := by
  induction n with
  | zero => exact seed_ne_zero c
  | succ n ih => exact div_ne_zero (mul_ne_zero ih (hu _)) (hu _)

/-- At the q-stage, every generator in both numerator factors is strictly earlier. -/
theorem moving_congr (U V : ℕ → RatFunc ℚ) (c : Bool) (n : ℕ)
    (h : ∀ j < stage c (.b (n+1)), U j = V j) : moving U c n = moving V c n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hb : stage c (.b (n+1)) < stage c (.b (n+2)) := by simp [stage]
    have hq : stage c (.q n) < stage c (.b (n+2)) := by simp [stage]; omega
    simp only [moving, ih (fun j hj => h j (hj.trans hb)), h _ hb, h _ hq]

/-- Numerator of the local return recurrence at the q-stage. -/
def returnNumerator {m : ℕ} (P : Prefix m) (c : Bool) (n : ℕ) : RatFunc ℚ :=
  moving P.generators c n * P.generators (stage c (.b (n+1)))

/-- The previous numerator is formed before selection of the q raw at this stage. -/
theorem moving_after_q {c : Bool} {n : ℕ} {P : Prefix (stage c (.q n))} (S : Next P) :
    moving S.append.generators c (n+1) =
      returnNumerator P c n / S.append.generators (stage c (.q n)) := by
  have hb : stage c (.b (n+1)) < stage c (.q n) := by simp [stage]
  rw [moving, moving_congr S.append.generators P.generators c n
    (fun j hj => S.generators_old j (hj.trans hb)), S.generators_old _ hb, returnNumerator]

def targetAt {m p : ℕ} [Fact p.Prime] (P : Prefix m) (c : Bool) (g : Generator)
    (e : RatFunc ℚ →+* ℚ_[p]) (order : ℕ) : ℚ_[p] :=
  match g with
  | .b _ => (p : ℚ_[p])^order
  | .q n => ReturnTargets.quotientTarget order (e (returnNumerator P c n))

def precisionAt {m p : ℕ} [Fact p.Prime] (P : Prefix m) (c : Bool) (g : Generator)
    (e : RatFunc ℚ →+* ℚ_[p]) (order : ℕ) : ℕ :=
  match g with
  | .b _ => 1
  | .q n => ReturnTargets.precision (n+1) order (e (returnNumerator P c n))

theorem targetAt_norm {m p : ℕ} [Fact p.Prime] (P : Prefix m) (c : Bool) (g : Generator)
    (e : RatFunc ℚ →+* ℚ_[p]) (order : ℕ) :
    ‖targetAt P c g e order‖ = (p : ℝ)^(-(order : ℤ)) := by
  cases g with
  | b n => exact Padic.norm_p_pow order
  | q n => exact ReturnTargets.quotientTarget_norm _ _

/-- Norms and refined return targets are imposed on every active branch.
The unused primary of a guard-only site carries no prescription. -/
def targets {m : ℕ} (P : Prefix m) (B : Batch) (sites : Table B.assigned.primes) :
    Targets B sites := by
  classical
  let site := siteAt B sites
  let e (i : B.indices) (b : Bool) (hb : MixedStageSelection.Active (site i).paired b) :=
    EvaluationDVR.evaluationHom (B.primeAt i) ((site i).branch b)
      ((site i).branch_transcendental b hb)
  let h (i : B.indices) (b : Bool) := requestedOrder m (B.guardAt i).birth b
  exact {
    value := fun i b => if hb : MixedStageSelection.Active (site i).paired b then
      targetAt P (decode m).1 (decode m).2 (e i b hb) (h i b) else 1
    precision := fun i b => if hb : MixedStageSelection.Active (site i).paired b then
      precisionAt P (decode m).1 (decode m).2 (e i b hb) (h i b) else 1
    nonzero := fun i b hb => by
      rw [dite_eq_left hb]
      apply norm_pos_iff.mp
      rw [targetAt_norm]
      exact zpow_pos (Nat.cast_pos.mpr (show (B.primeAt i).Prime from Fact.out).pos) _ }

theorem target_norm {m : ℕ} (P : Prefix m) (B : Batch) (sites : Table B.assigned.primes)
    (i : B.indices) (b : Bool) (hb : MixedStageSelection.Active (siteAt B sites i).paired b) :
    ‖(targets P B sites).value i b‖ =
      (B.primeAt i : ℝ)^(-(requestedOrder m (B.guardAt i).birth b : ℤ)) := by
  classical
  simp only [targets, dite_eq_left hb]
  exact targetAt_norm ..

/-- At a q-stage both the target and its precision use the evaluated numerator
of the very same colour's recurrence. -/
theorem targets_at_q (c : Bool) (n : ℕ) (P : Prefix (stage c (.q n))) (B : Batch)
    (sites : Table B.assigned.primes) (i : B.indices) (b : Bool)
    (hb : MixedStageSelection.Active (siteAt B sites i).paired b) :
    let site := siteAt B sites i
    let r := EvaluationDVR.evaluationHom (B.primeAt i) (site.branch b)
      (site.branch_transcendental b hb) (returnNumerator P c n)
    let h := requestedOrder (stage c (.q n)) (B.guardAt i).birth b
    (targets P B sites).value i b = ReturnTargets.quotientTarget h r ∧
      (targets P B sites).precision i b = ReturnTargets.precision (n+1) h r := by
  classical
  simp [targets, hb, targetAt, precisionAt]

end UnconditionalCounterexample.TwoChains
