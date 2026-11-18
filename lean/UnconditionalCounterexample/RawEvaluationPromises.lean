import UnconditionalCounterexample.CombinedGuardStep
import UnconditionalCounterexample.SignedConstant

/-!
# Global raw and normalized evaluation promises

The guard argument uses the paper's actual logarithmic assignment chain. A
strong induction converts normalized current-stage guard promises to raw unit
evaluations; later guards use old-raw avoidance at their first assignment.
Outside ordinary coefficient support, the actual signed constant and residue
zero of the primary give unit evaluation. No independent raw or guard recursion
is constructed here; SequenceValuations supplies these inputs from one chain.
-/

namespace UnconditionalCounterexample.RawEvaluationPromises

open Polynomial GuardSupport PaperGuardStages CombinedGuardStep

/-- Ordinary processed guards and the current auxiliary guard exhaust the
completed finite batch, with exactly their originally chosen values. -/
theorem current_raw_norm_one_on_batch (B : Batch) (F : ℚ[X])
    (hprocessed : ∀ (p : PrimeIndex) (hp : p ∈ B.processed.primes),
      ‖F.eval₂ (algebraMap ℚ ℚ_[p.val]) (B.processed.guard p hp).value.val‖ = 1)
    (haux : ‖F.eval₂ (algebraMap ℚ ℚ_[B.auxiliary.val]) B.auxiliary_guard.value.val‖ = 1) :
    ∀ (p : PrimeIndex) (hp : p ∈ B.assigned.primes),
      ‖F.eval₂ (algebraMap ℚ ℚ_[p.val]) (B.assigned.guard p hp).value.val‖ = 1 := by
  intro p hp
  rcases Finset.mem_insert.mp hp with heq | hpP
  · subst p
    rw [B.assigned_auxiliary]
    exact haux
  · rw [B.assigned_old p hpP]
    exact hprocessed p hpP

/-- Every raw has unit norm at every global guard. At guards already assigned
when it is chosen, use the current finite-stage promise. At later guards, use
the actual earlier-raw avoidance promise at that guard's first assignment. -/
theorem norm_one_at_all_global_guards
    (C : ApproximationChain) (F : ℕ → ℚ[X])
    (hcurrent : ∀ (n : ℕ) (p : PrimeIndex) (hp : p ∈ (C.assignments n).primes),
      ‖(F n).eval₂ (algebraMap ℚ ℚ_[p.val]) ((C.assignments n).guard p hp).value.val‖ = 1)
    (hlater : ∀ (k : ℕ) (p : PrimeIndex) (hp : p ∈ (C.assignments (k + 1)).primes),
      p ∉ (C.assignments k).primes → ∀ n ≤ k,
      ‖(F n).eval₂ (algebraMap ℚ ℚ_[p.val]) ((C.assignments (k + 1)).guard p hp).value.val‖ = 1) :
    ∀ (n : ℕ) (p : PrimeIndex), ‖(F n).eval₂ (algebraMap ℚ ℚ_[p.val]) (C.value p).val‖ = 1 := by
  intro n p
  by_cases hp : p ∈ (C.assignments n).primes
  · rw [← C.value_agrees n p hp]
    exact hcurrent n p hp
  · have hnb : n < C.birth p := by
      by_contra hn
      exact hp ((C.birth_le_iff_mem p n).mp (by omega))
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : C.birth p ≠ 0)
    have hpk : p ∈ (C.assignments (k + 1)).primes := by
      simpa only [hk] using C.birth_mem p
    have hnprev : p ∉ (C.assignments k).primes :=
      C.not_mem_before_birth p (by omega)
    have hu := hlater k p hpk hnprev n (by omega)
    rw [C.value_agrees (k + 1) p hpk] at hu
    exact hu

/-- Explicitly realize the current-stage promise from the same recorded batch. -/
theorem current_raw_norm_one_of_batches
    (C : ApproximationChain) (B : ℕ → Batch) (hB : ∀ n, C.assignments n = (B n).assigned)
    (F : ℕ → ℚ[X])
    (hprocessed : ∀ (n : ℕ) (p : PrimeIndex) (hp : p ∈ (B n).processed.primes),
      ‖(F n).eval₂ (algebraMap ℚ ℚ_[p.val]) ((B n).processed.guard p hp).value.val‖ = 1)
    (haux : ∀ n,
      ‖(F n).eval₂ (algebraMap ℚ ℚ_[(B n).auxiliary.val]) (B n).auxiliary_guard.value.val‖ = 1) :
    ∀ (n : ℕ) (p : PrimeIndex) (hp : p ∈ (C.assignments n).primes),
      ‖(F n).eval₂ (algebraMap ℚ ℚ_[p.val]) ((C.assignments n).guard p hp).value.val‖ = 1 := by
  intro n p hp
  have hpB : p ∈ (B n).assigned.primes := by simpa only [hB n] using hp
  simpa only [hB n] using current_raw_norm_one_on_batch (B n) (F n) (hprocessed n) (haux n) p hpB

/-- Rational polynomial inclusion followed by the actual evaluation embedding
is the usual polynomial evaluation. -/
theorem evaluationHom_polynomial {p : ℕ} [Fact p.Prime]
    (a : ℚ_[p]) (ha : Transcendental ℚ a) (F : ℚ[X]) :
    EvaluationDVR.evaluationHom p a ha (algebraMap ℚ[X] (RatFunc ℚ) F) =
      F.eval₂ (algebraMap ℚ ℚ_[p]) a := by
  simp [EvaluationDVR.evaluationHom, LocalEvaluation.evalAt,
    RatFunc.algEquivOfTranscendental_algebraMap, ← aeval_def]

/-- The preceding norm promises are literal statements about the same
restricted guard valuations used in the domain intersection. -/
theorem raw_guard_valuation_one
    (C : ApproximationChain) (F : ℕ → ℚ[X])
    (hcurrent : ∀ (n : ℕ) (p : PrimeIndex) (hp : p ∈ (C.assignments n).primes),
      ‖(F n).eval₂ (algebraMap ℚ ℚ_[p.val]) ((C.assignments n).guard p hp).value.val‖ = 1)
    (hlater : ∀ (k : ℕ) (p : PrimeIndex) (hp : p ∈ (C.assignments (k + 1)).primes),
      p ∉ (C.assignments k).primes → ∀ n ≤ k,
      ‖(F n).eval₂ (algebraMap ℚ ℚ_[p.val]) ((C.assignments (k + 1)).guard p hp).value.val‖ = 1) :
    ∀ (n : ℕ) (p : PrimeIndex), EvaluationDVR.valuation p.val
      (guardEvaluation C.value C.value_transcendental p)
      (algebraMap ℚ[X] (RatFunc ℚ) (F n)) = 1 := by
  intro n p
  apply GuardSupport.mulValuation_eq_one_of_norm_eq_one
  change ‖EvaluationDVR.evaluationHom p.val (C.value p).val (C.value_transcendental p)
    (algebraMap ℚ[X] (RatFunc ℚ) (F n))‖ = 1
  rw [evaluationHom_polynomial]
  exact norm_one_at_all_global_guards C F hcurrent hlater n p

/-- At a primary argument of residue zero, an integral polynomial with unit
constant term has unit evaluation. -/
theorem eval_unit_of_residue_zero {p : ℕ} [Fact p.Prime]
    (G : ℤ_[p][X]) (α : ℤ_[p]) (hα : PadicInt.toZMod α = 0)
    (hconst : IsUnit (G.coeff 0)) : IsUnit (G.eval α) := by
  apply (padicInt_isUnit_iff_toZMod_ne_zero _).mpr
  rw [← eval₂_at_apply, hα, eval₂_at_zero]
  exact (padicInt_isUnit_iff_toZMod_ne_zero _).mp hconst

/-- The denominator-support invariant and unit constant term imply the actual
rational raw evaluation is a unit at any primary of residue zero outside support. -/
theorem norm_one_at_unassigned_primary
    (A : Assignment) (F : ℚ[X]) (hF : F.Monic)
    (hsupp : ∀ n (p : PrimeIndex), p.val ∣ (F.coeff n).den → p ∈ A.primes)
    (p : PrimeIndex) (hp : p ∉ A.primes)
    (hconst : ‖(F.coeff 0 : ℚ_[p.val])‖ = 1)
    (α : ℤ_[p.val]) (hα : PadicInt.toZMod α = 0) :
    ‖F.eval₂ (algebraMap ℚ ℚ_[p.val]) α.val‖ = 1 := by
  obtain ⟨G, hG⟩ := RationalGuardStage.exists_models A (fun _ : Unit => F)
    (fun _ => hF) (fun _ => hsupp)
  have hmap := (hG p hp ()).1
  have hcoeff := congrArg (fun P : ℚ_[p.val][X] => P.coeff 0) hmap
  simp only [coeff_map] at hcoeff
  have hunit : IsUnit ((G p ()).coeff 0) := by
    apply PadicInt.isUnit_iff.mpr
    change ‖(algebraMap ℤ_[p.val] ℚ_[p.val]) ((G p ()).coeff 0)‖ = 1
    rw [hcoeff]
    exact hconst
  exact RationalGuardStage.norm_eval_eq_one_of_integral_model F (G p ()) hmap α
    (eval_unit_of_residue_zero (G p ()) α hα hunit)

/-- Every positive-valuation integral argument has residue zero. -/
theorem residue_zero_of_positive_valuation {p : ℕ} [Fact p.Prime]
    (α : ℤ_[p]) (hval : 0 < α.val.valuation) : PadicInt.toZMod α = 0 := by
  rw [← RingHom.mem_ker, PadicInt.ker_toZMod, IsLocalRing.mem_maximalIdeal,
    mem_nonunits_iff, PadicInt.not_isUnit_iff]
  change ‖α.val‖ < 1
  have ha0 : α.val ≠ 0 := by
    intro hz
    simp only [hz, Padic.valuation_zero, lt_self_iff_false] at hval
  rw [Padic.norm_eq_zpow_neg_valuation ha0]
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  simpa only [zpow_zero] using
    (zpow_lt_zpow_right₀ hp1 (show -α.val.valuation < (0 : ℤ) by omega))

/-- This includes the exceptional valuation-two first primary. -/
theorem primary_residue_zero (j : ℕ) :
    PadicInt.toZMod (PrimaryChoices.primary j) = 0 := by
  apply residue_zero_of_positive_valuation
  rw [PrimaryChoices.primary_valuation]
  unfold PrimaryChoices.order
  split <;> norm_num

/-- Every chosen raw has unit norm at each primary outside its actual ordinary
coefficient-support set, including current auxiliary and all later primaries. -/
theorem raw_norm_one_at_later_primaries
    (B : ℕ → Batch) (F : ℕ → ℚ[X]) (hF : ∀ n, (F n).Monic)
    (hsupp : ∀ n k (p : PrimeIndex), p.val ∣ ((F n).coeff k).den → p ∈ (B n).processed.primes)
    (hconst : ∀ n (p : PrimeIndex), p ∉ (B n).processed.primes →
      ‖((F n).coeff 0 : ℚ_[p.val])‖ = 1) :
    ∀ n j, PrimaryChoices.primes j ∉ (B n).processed.primes →
      ‖(F n).eval₂ (algebraMap ℚ ℚ_[(PrimaryChoices.primes j).val])
        (PrimaryChoices.primary j).val‖ = 1 := by
  intro n j hj
  exact norm_one_at_unassigned_primary (B n).processed (F n) (hF n) (hsupp n)
    (PrimaryChoices.primes j) hj (hconst n _ hj) (PrimaryChoices.primary j) (primary_residue_zero j)

/-- The later-primary promise concerns the actual restricted primary valuation. -/
theorem raw_valuation_one_at_later_primaries
    (B : ℕ → Batch) (F : ℕ → ℚ[X]) (hF : ∀ n, (F n).Monic)
    (hsupp : ∀ n k (p : PrimeIndex), p.val ∣ ((F n).coeff k).den → p ∈ (B n).processed.primes)
    (hconst : ∀ n (p : PrimeIndex), p ∉ (B n).processed.primes →
      ‖((F n).coeff 0 : ℚ_[p.val])‖ = 1) :
    ∀ n j, PrimaryChoices.primes j ∉ (B n).processed.primes →
      EvaluationDVR.evaluationValuation (PrimaryChoices.primes j).val
        (PrimaryChoices.primary j).val (PrimaryChoices.primary_transcendental j)
        (algebraMap ℚ[X] (RatFunc ℚ) (F n)) = 1 := by
  intro n j hj
  apply GuardSupport.mulValuation_eq_one_of_norm_eq_one
  change ‖EvaluationDVR.evaluationHom (PrimaryChoices.primes j).val
    (PrimaryChoices.primary j).val (PrimaryChoices.primary_transcendental j)
    (algebraMap ℚ[X] (RatFunc ℚ) (F n))‖ = 1
  rw [evaluationHom_polynomial]
  exact raw_norm_one_at_later_primaries B F hF hsupp hconst n j hj

/-- The paper's prescribed signed constant supplies the outside-support unit
constant hypothesis, so later primary promises require no additional unit input. -/
theorem raw_valuation_one_at_later_primaries_of_signed_constants
    (B : ℕ → Batch) (F : ℕ → ℚ[X]) (hF : ∀ n, (F n).Monic)
    (hsupp : ∀ n k (p : PrimeIndex), p.val ∣ ((F n).coeff k).den → p ∈ (B n).processed.primes)
    (d : ℕ → ℕ) (N : (n : ℕ) → (B n).processed.primes → ℕ)
    (hconstant : ∀ n, (F n).coeff 0 =
      SignedConstant.constant (fun q : (B n).processed.primes => q.val.val) (N n) (d n)) :
    ∀ n j, PrimaryChoices.primes j ∉ (B n).processed.primes →
      EvaluationDVR.evaluationValuation (PrimaryChoices.primes j).val
        (PrimaryChoices.primary j).val (PrimaryChoices.primary_transcendental j)
        (algebraMap ℚ[X] (RatFunc ℚ) (F n)) = 1 := by
  apply raw_valuation_one_at_later_primaries B F hF hsupp
  intro n p hp
  rw [hconstant n]
  apply SignedConstant.norm_constant_at_unassigned
    (fun q : (B n).processed.primes => q.val.val) (fun q => q.val.property) (N n) (d n) p.val
  intro q heq
  apply hp
  have hqp : q.val = p := Subtype.ext heq
  exact hqp ▸ q.property

/-- The actual shifted-Eisenstein model supplies the current auxiliary guard
promise for the very same rational raw polynomial. -/
theorem current_auxiliary_norm_one_of_shifted_model (B : Batch) (F : ℚ[X])
    (G : ℤ_[B.auxiliary.val][X]) (d : ℕ)
    (hmap : G.map (algebraMap ℤ_[B.auxiliary.val] ℚ_[B.auxiliary.val]) =
      F.map (algebraMap ℚ ℚ_[B.auxiliary.val]))
    (hred : G.map (PadicInt.toZModPow 1) = (X - C 1) ^ d) :
    ‖F.eval₂ (algebraMap ℚ ℚ_[B.auxiliary.val]) B.auxiliary_guard.value.val‖ = 1 :=
  RationalGuardStage.norm_eval_eq_one_of_integral_model F G hmap B.auxiliary_guard.value
    (PaperGuardStages.auxiliary_eval_unit G d hred B.auxiliary_guard.value B.auxiliary_away_one)

/-- The actual source denominator is a power of the product of all earlier raws. -/
noncomputable def rawDenominator (F : ℕ → ℚ[X]) (E : ℕ → ℕ) (n : ℕ) : ℚ[X] :=
  (∏ h : Fin n, F h.val) ^ E n

theorem denominator_norm_one {p : ℕ} [Fact p.Prime]
    (F : ℕ → ℚ[X]) (E : ℕ → ℕ) (n : ℕ) (a : ℚ_[p])
    (hF : ∀ h < n, ‖(F h).eval₂ (algebraMap ℚ ℚ_[p]) a‖ = 1) :
    ‖(rawDenominator F E n).eval₂ (algebraMap ℚ ℚ_[p]) a‖ = 1 := by
  simp only [rawDenominator, eval₂_pow, eval₂_finsetProd, norm_pow, norm_prod]
  have heq : (∏ h : Fin n, ‖(F h.val).eval₂ (algebraMap ℚ ℚ_[p]) a‖) = 1 := by
    apply Finset.prod_eq_one
    intro h _
    exact hF h.val h.isLt
  rw [heq, one_pow]

/-- An already processed guard has exactly its global value. -/
theorem processed_value_agrees
    (C : ApproximationChain) (B : ℕ → Batch) (hB : ∀ n, C.assignments n = (B n).assigned)
    (n : ℕ) (p : PrimeIndex) (hp : p ∈ (B n).processed.primes) :
    ((B n).processed.guard p hp).value = C.value p := by
  have ha : p ∈ (C.assignments n).primes := by
    rw [hB n]
    exact (B n).processed_subset_assigned hp
  have hv := C.value_agrees n p ha
  simp only [hB n, (B n).assigned_old p hp] at hv
  exact hv

theorem auxiliary_value_agrees
    (C : ApproximationChain) (B : ℕ → Batch) (hB : ∀ n, C.assignments n = (B n).assigned)
    (n : ℕ) : (B n).auxiliary_guard.value = C.value (B n).auxiliary := by
  have ha : (B n).auxiliary ∈ (C.assignments n).primes := by
    rw [hB n]
    exact Finset.mem_insert_self _ _
  have hv := C.value_agrees n (B n).auxiliary ha
  simp only [hB n, (B n).assigned_auxiliary] at hv
  exact hv

/-- Later guard avoidance is an actual finite-stage promise at its first
assignment; no all-prime unit hypothesis is required. -/
theorem later_guard_norm_one
    (C : ApproximationChain) (F : ℕ → ℚ[X])
    (hlater : ∀ (k : ℕ) (p : PrimeIndex) (hp : p ∈ (C.assignments (k + 1)).primes),
      p ∉ (C.assignments k).primes → ∀ n ≤ k,
      ‖(F n).eval₂ (algebraMap ℚ ℚ_[p.val]) ((C.assignments (k + 1)).guard p hp).value.val‖ = 1)
    (n : ℕ) (p : PrimeIndex) (hp : p ∉ (C.assignments n).primes) :
    ‖(F n).eval₂ (algebraMap ℚ ℚ_[p.val]) (C.value p).val‖ = 1 := by
  have hnb : n < C.birth p := by
    by_contra hn
    exact hp ((C.birth_le_iff_mem p n).mp (by omega))
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : C.birth p ≠ 0)
  have hpk : p ∈ (C.assignments (k + 1)).primes := by simpa only [hk] using C.birth_mem p
  have hnprev : p ∉ (C.assignments k).primes := C.not_mem_before_birth p (by omega)
  have hu := hlater k p hpk hnprev n (by omega)
  rw [C.value_agrees (k + 1) p hpk] at hu
  exact hu

/-- Strong induction converts the selector's normalized guard profiles into
unit norms for each actual raw at every global guard, including old guards,
the current auxiliary prime, and all later assignments. -/
theorem raw_norm_one_of_normalized_stage_promises
    (C : ApproximationChain) (B : ℕ → Batch) (hB : ∀ n, C.assignments n = (B n).assigned)
    (F : ℕ → ℚ[X]) (E : ℕ → ℕ)
    (hprocessed : ∀ (n : ℕ) (p : PrimeIndex) (hp : p ∈ (B n).processed.primes),
      ‖(F n).eval₂ (algebraMap ℚ ℚ_[p.val]) ((B n).processed.guard p hp).value.val /
        (rawDenominator F E n).eval₂ (algebraMap ℚ ℚ_[p.val])
          ((B n).processed.guard p hp).value.val‖ = 1)
    (haux : ∀ n, ‖(F n).eval₂ (algebraMap ℚ ℚ_[(B n).auxiliary.val])
      (B n).auxiliary_guard.value.val‖ = 1)
    (hlater : ∀ (k : ℕ) (p : PrimeIndex) (hp : p ∈ (C.assignments (k + 1)).primes),
      p ∉ (C.assignments k).primes → ∀ n ≤ k,
      ‖(F n).eval₂ (algebraMap ℚ ℚ_[p.val]) ((C.assignments (k + 1)).guard p hp).value.val‖ = 1) :
    ∀ (n : ℕ) (p : PrimeIndex),
      ‖(F n).eval₂ (algebraMap ℚ ℚ_[p.val]) (C.value p).val‖ = 1 := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro p
    by_cases hp : p ∈ (C.assignments n).primes
    · have hpB : p ∈ (B n).assigned.primes := by simpa only [hB n] using hp
      rcases Finset.mem_insert.mp hpB with heq | hpP
      · subst p
        rw [← auxiliary_value_agrees C B hB n]
        exact haux n
      · have hn := hprocessed n p hpP
        rw [processed_value_agrees C B hB n p hpP, norm_div,
          denominator_norm_one F E n (C.value p).val (fun k hk => ih k hk p), div_one] at hn
        exact hn
    · exact later_guard_norm_one C F hlater n p hp

/-- The normalized finite profiles yield literal global guard valuations of
all selected raw polynomials. -/
theorem raw_guard_valuation_one_of_normalized_stage_promises
    (C : ApproximationChain) (B : ℕ → Batch) (hB : ∀ n, C.assignments n = (B n).assigned)
    (F : ℕ → ℚ[X]) (E : ℕ → ℕ)
    (hprocessed : ∀ (n : ℕ) (p : PrimeIndex) (hp : p ∈ (B n).processed.primes),
      ‖(F n).eval₂ (algebraMap ℚ ℚ_[p.val]) ((B n).processed.guard p hp).value.val /
        (rawDenominator F E n).eval₂ (algebraMap ℚ ℚ_[p.val])
          ((B n).processed.guard p hp).value.val‖ = 1)
    (haux : ∀ n, ‖(F n).eval₂ (algebraMap ℚ ℚ_[(B n).auxiliary.val])
      (B n).auxiliary_guard.value.val‖ = 1)
    (hlater : ∀ (k : ℕ) (p : PrimeIndex) (hp : p ∈ (C.assignments (k + 1)).primes),
      p ∉ (C.assignments k).primes → ∀ n ≤ k,
      ‖(F n).eval₂ (algebraMap ℚ ℚ_[p.val]) ((C.assignments (k + 1)).guard p hp).value.val‖ = 1) :
    ∀ (n : ℕ) (p : PrimeIndex), EvaluationDVR.valuation p.val
      (guardEvaluation C.value C.value_transcendental p)
      (algebraMap ℚ[X] (RatFunc ℚ) (F n)) = 1 := by
  intro n p
  apply GuardSupport.mulValuation_eq_one_of_norm_eq_one
  change ‖EvaluationDVR.evaluationHom p.val (C.value p).val (C.value_transcendental p)
    (algebraMap ℚ[X] (RatFunc ℚ) (F n))‖ = 1
  rw [evaluationHom_polynomial]
  exact raw_norm_one_of_normalized_stage_promises C B hB F E hprocessed haux hlater n p

/-- The very same raw guard units imply unit valuation for every normalized
generator, with the literal common old-raw denominator. -/
theorem normalized_guard_valuation_one
    (C : ApproximationChain) (F : ℕ → ℚ[X]) (E : ℕ → ℕ)
    (hraw : ∀ (n : ℕ) (p : PrimeIndex),
      ‖(F n).eval₂ (algebraMap ℚ ℚ_[p.val]) (C.value p).val‖ = 1) :
    ∀ (n : ℕ) (p : PrimeIndex), EvaluationDVR.valuation p.val
      (guardEvaluation C.value C.value_transcendental p)
      (algebraMap ℚ[X] (RatFunc ℚ) (F n) /
        algebraMap ℚ[X] (RatFunc ℚ) (rawDenominator F E n)) = 1 := by
  intro n p
  apply GuardSupport.mulValuation_eq_one_of_norm_eq_one
  change ‖EvaluationDVR.evaluationHom p.val (C.value p).val (C.value_transcendental p)
    (algebraMap ℚ[X] (RatFunc ℚ) (F n) /
      algebraMap ℚ[X] (RatFunc ℚ) (rawDenominator F E n))‖ = 1
  rw [map_div₀, evaluationHom_polynomial, evaluationHom_polynomial, norm_div,
    hraw n p, denominator_norm_one F E n (C.value p).val (fun j _ => hraw j p), div_one]

end UnconditionalCounterexample.RawEvaluationPromises
