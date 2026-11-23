import UnconditionalCounterexample.Variations.UnivariateBirths
import UnconditionalCounterexample.MixedSequenceValuations

/-!
# Normalized values and returns on the adaptive sequence

The same global generator has the prescribed norm and relative precision at every
processed site. A guard-unit prescription gives unit norms at all guards. Earlier
generators are units at a newly requested primary screened against the prefix.
-/

noncomputable section
namespace UnconditionalCounterexample.Variations.Univariate

open Polynomial GuardSupport PrimaryChoices CombinedGuardStep RecursivePrefix ConstructionWords
open RawEvaluationPromises MixedStageSelection

set_option backward.isDefEq.respectTransparency false

variable (R : Requirements)

def Site.evaluate {p : PrimeIndex} (site : Site p) (b : Bool) (hb : Active site.paired b) :
    RatFunc ℚ →+* ℚ_[p.val] :=
  EvaluationDVR.evaluationHom p.val (site.branch b) (site.branch_transcendental b hb)

abbrev actualTargets (n : ℕ) := R.targets ((chain R).approx n) (table R n) (selection R n).batch
  (extend R ((chain R).approx n) (table R n) (selection R n).batch)

theorem generators_eq_quotient (n : ℕ) :
    (chain R).generators n = algebraMap ℚ[X] (RatFunc ℚ) ((chain R).raw n) /
      algebraMap ℚ[X] (RatFunc ℚ) (rawDenominator (chain R).raw (chain R).exponent n) := by
  unfold RecursivePrefix.Chain.generators ScheduledRecovery.generators RawWords.normalizedFactor rawDenominator
  dsimp only
  rw [← Finset.prod_pow,
    Fin.prod_univ_eq_prod_range (fun j => (chain R).raw j ^ (chain R).exponent n) n, map_prod]
  simp only [map_pow]

theorem denominator_eq_plan (n : ℕ) :
    rawDenominator (chain R).raw (chain R).exponent n = (selection R n).plan.rawDen := by
  unfold rawDenominator DegreePlan.rawDen
  rw [← Finset.prod_pow, (chain R).exponent_eq_selected]
  apply Finset.prod_congr rfl
  intro j _
  rw [(chain R).rawAt_agrees n j.val j.isLt]
  rfl

/-- The normalized value in the global ring equals the chosen target in norm
and the quotient target/value is one to the requested relative precision. -/
theorem processed_value (n : ℕ) (i : (selection R n).batch.indices) (b : Bool)
    (hb : Active (permanentSite R (primes i.val)).paired b) :
    let e := (permanentSite R (primes i.val)).evaluate b hb ((chain R).generators n)
    let t := actualTargets R n
    let v : ℚ_[(primes i.val).val] := t.value i b
    ‖e‖ = ‖v‖ ∧
      (v / e - 1) / ((primes i.val).val : ℚ_[(primes i.val).val]) ^ t.precision i b
        ∈ PadicInt.subring (primes i.val).val := by
  let sel := selection R n
  let site := selectionSite R n i
  have hx := selectionSite_eq R n i
  have hb' : Active site.paired b := by change Active (selectionSite R n i).paired b; rwa [hx]
  have h := ((sel.choice.witnesses.2.2.2.2.2.1 i).2.1 b hb').2
  have hmap := ShiftedEisenstein.monicFamily_map (algebraMap ℚ ℚ_[(primes i.val).val])
    (sel.plan.degree - 1) sel.constant sel.choice.coeff
  have hcast (r : ℚ) : algebraMap ℚ ℚ_[(primes i.val).val] r =
      (r : ℚ_[(primes i.val).val]) := by
    simpa only [Rat.cast_id] using map_ratCast (algebraMap ℚ ℚ_[(primes i.val).val]) r
  simp only [hcast] at hmap
  let val := (sel.raw.map (algebraMap ℚ ℚ_[(primes i.val).val])).eval (site.branch b) /
    sel.plan.rawDen.eval₂ (algebraMap ℚ ℚ_[(primes i.val).val]) (site.branch b)
  have he : (permanentSite R (primes i.val)).evaluate b hb ((chain R).generators n) = val := by
    unfold Site.evaluate
    rw [generators_eq_quotient, ReturnTargets.evaluation_normalized_polynomial,
      denominator_eq_plan, raw_eq_selection]
    simp only [val, eval_map, site, hx, sel]
  dsimp only
  rw [he]
  simp only [val, Selection.raw, hmap]
  simp only [site, actualTargets, selectionSite, DegreePlan.denValue, Selection.constant, Batch.primeAt, sel] at h ⊢
  exact h

private theorem later_raw_norm (k : ℕ) (p : PrimeIndex)
    (hp : p ∈ ((chain R).guardChain.assignments (k+1)).primes)
    (hn : p ∉ ((chain R).guardChain.assignments k).primes) (j : ℕ) (hj : j ≤ k) :
    ‖((chain R).raw j).eval₂ (algebraMap ℚ ℚ_[p.val])
      (((chain R).guardChain.assignments (k+1)).guard p hp).value.val‖ = 1 := by
  have h := ((selection R (k+1)).progress.new_guard p hp hn).2 ⟨j, by omega⟩
  rw [(chain R).raw_agrees] at h
  exact h

private theorem auxiliary_raw_norm (n : ℕ) :
    ‖((chain R).raw n).eval₂ (algebraMap ℚ ℚ_[(selection R n).batch.auxiliary.val])
      (selection R n).batch.auxiliary_guard.value.val‖ = 1 := by
  let s := selection R n
  obtain ⟨G, _, hmap, hred, _⟩ := s.choice.witnesses.2.2.2.2.2.2.2
  rw [raw_eq_selection]
  exact current_auxiliary_norm_one_of_shifted_model s.batch s.raw G
    (s.plan.degree - 1 + 1) hmap hred

/-- Unit norms at all actual guards, including at the fresh Eisenstein prime
and at guards introduced after the polynomial was selected. -/
theorem raw_guard_norm (ht : ∀ n i, ‖(actualTargets R n).value i true‖ = 1) (n : ℕ)
    (p : PrimeIndex) :
    ‖((chain R).raw n).eval₂ (algebraMap ℚ ℚ_[p.val]) (permanentSite R p).guard.val‖ = 1 := by
  rw [permanent_guard_eq]
  apply raw_norm_one_of_normalized_stage_promises (chain R).guardChain
    (fun n => (selection R n).batch) (fun _ => rfl) (chain R).raw (chain R).exponent
    _ (auxiliary_raw_norm R) (later_raw_norm R) n p
  intro k q hq
  obtain ⟨j, rfl⟩ := primes.surjective q
  let i : (selection R k).batch.indices := ⟨j, ((selection R k).batch.mem_indices j).mpr hq⟩
  have h := (processed_value R k i true (Or.inl rfl)).1.trans (ht k i)
  unfold Site.evaluate at h
  rw [generators_eq_quotient, ReturnTargets.evaluation_normalized_polynomial] at h
  have eqg := processed_value_agrees (chain R).guardChain (fun m => (selection R m).batch)
    (fun _ => rfl) k (primes j) hq
  have heq : (permanentSite R (primes j)).branch true =
      ((selection R k).batch.processed.guard (primes j) hq).value.val :=
    congrArg Subtype.val ((permanent_guard_eq R (primes j)).trans eqg.symm)
  exact heq ▸ h

theorem generator_guard_norm (ht : ∀ n i, ‖(actualTargets R n).value i true‖ = 1)
    (n : ℕ) (p : PrimeIndex) :
    ‖(permanentSite R p).evaluate true (Or.inl rfl) ((chain R).generators n)‖ = 1 := by
  unfold Site.evaluate
  rw [generators_eq_quotient, ReturnTargets.evaluation_normalized_polynomial, norm_div]
  exact (congrArg₂ HDiv.hDiv (raw_guard_norm R ht n p)
    (denominator_norm_one _ _ n (permanentSite R p).guard.val
      (fun k _ => raw_guard_norm R ht k p))).trans (div_one _)

/-- A requested primary at which the prefix raws are units also sees all
prefix normalized generators as units, including every signed denominator. -/
theorem generator_norm_before_birth (S : Schedule) {m : ℕ} (p : PrimeIndex)
    (h : p ∈ (S.chosen m).primes) (hp : ((S.chosen m).site p h).paired)
    (hold : ∀ j : Fin m, ‖(((chain S.requirements).approx m).raw j).eval₂
      (algebraMap ℚ ℚ_[p.val]) (((S.chosen m).site p h).branch false)‖ = 1)
    (k : ℕ) (hk : k < m) :
    ‖(permanentSite S.requirements p).evaluate false (Or.inr (by
      rwa [S.permanentSite_requested m p h])) ((chain S.requirements).generators k)‖ = 1 := by
  unfold Site.evaluate
  rw [generators_eq_quotient, ReturnTargets.evaluation_normalized_polynomial,
    S.permanentSite_requested m p h, norm_div]
  have hnorm (j : ℕ) (hj : j < m) :
      ‖((chain S.requirements).raw j).eval₂ (algebraMap ℚ ℚ_[p.val])
        (((S.chosen m).site p h).branch false)‖ = 1 := by
    have ht := hold ⟨j,hj⟩
    rwa [(chain S.requirements).raw_agrees] at ht
  rw [hnorm k hk, denominator_norm_one _ _ _ _ (fun j hj => hnorm j (lt_trans hj hk)), div_one]

end UnconditionalCounterexample.Variations.Univariate
