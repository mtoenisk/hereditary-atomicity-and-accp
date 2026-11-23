import UnconditionalCounterexample.Variations.TwoChainValues
import UnconditionalCounterexample.Variations.TwoChainReturns
import UnconditionalCounterexample.Variations.UnivariateValues
import UnconditionalCounterexample.ConstructionReturns

/-!
# Refined returns of the selected moving atoms

At a processed q-stage a unit q generator and a unit previous numerator
activate the refined target. Prefix agreement transports this target to
the same moving element used in the domain.
-/

noncomputable section
namespace UnconditionalCounterexample.TwoChains

open GuardSupport Filter PrimaryChoices NormalizedWords
open Variations Univariate TwoChainSchedule

private theorem previous_numerator (c : Bool) (n : ℕ) :
    returnNumerator ((chain requirements).approx (stage c (.q n))) c n =
      moving generators c n * generators (stage c (.b (n+1))) := by
  have hb : stage c (.b (n+1)) < stage c (.q n) := by simp [stage]
  unfold returnNumerator
  rw [moving_congr _ generators c n (fun j hj =>
    (chain requirements).generators_agree _ j (hj.trans hb)),
    (chain requirements).generators_agree _ _ hb]

/-- Selected branch return at one raw q-stage. Both unit hypotheses are
verified from the profiles once the chosen primary is behind the moving pivot. -/
theorem q_return_of_unit_norms (c : Bool) (n : ℕ)
    (i : (selection requirements (stage c (.q n))).batch.indices) (b : Bool)
    (hb : MixedStageSelection.Active (permanentSite requirements (primes i.val)).paired b)
    (hnum : ‖(permanentSite requirements (primes i.val)).evaluate b hb
      (moving generators c n * generators (stage c (.b (n+1))))‖ = 1)
    (hq : ‖(permanentSite requirements (primes i.val)).evaluate b hb
      (generators (stage c (.q n)))‖ = 1) :
    ((permanentSite requirements (primes i.val)).evaluate b hb (moving generators c (n+1)) - 1) /
      ((primes i.val).val : ℚ_[(primes i.val).val])^(n+1) ∈ PadicInt.subring (primes i.val).val := by
  let k := stage c (.q n)
  let B := (selection requirements k).batch
  let P := (chain requirements).approx k
  let sites := extend requirements P (table requirements k) B
  let E := (permanentSite requirements (primes i.val)).evaluate b hb
  let u := E (moving generators c n * generators (stage c (.b (n+1))))
  let h := requestedOrder k (B.guardAt i).birth b
  have hs : siteAt B sites i = permanentSite requirements (primes i.val) := selectionSite_eq ..
  have hb' : MixedStageSelection.Active (siteAt B sites i).paired b := hs ▸ hb
  have hraw := targets_at_q c n P B sites i b hb'
  have hvalue : (actualTargets requirements k).value i b = ReturnTargets.quotientTarget h u := by
    change (targets P B sites).value i b = _
    rw [hraw.1]
    congr 1
    dsimp only [u, E, Site.evaluate]
    rw [← previous_numerator]
    congr 2
    exact congrArg (fun s : Site (primes i.val) => s.branch b) hs
  have hprecision : (actualTargets requirements k).precision i b = ReturnTargets.precision (n+1) h u := by
    change (targets P B sites).precision i b = _
    rw [hraw.2]
    congr 1
    dsimp only [u, E, Site.evaluate]
    rw [← previous_numerator]
    congr 2
    exact congrArg (fun s : Site (primes i.val) => s.branch b) hs
  have hp := processed_value requirements k i b hb
  dsimp only at hp
  rw [hvalue, hprecision] at hp
  have ht : ‖(1 : ℚ_[(primes i.val).val])‖ = ‖ReturnTargets.quotientTarget h u‖ := by
    rw [norm_one, ← hp.1, hq]
  have hval := ReturnTargets.valuation_of_target_norm h u 1 ht
  have href : ReturnTargets.IsRefined h u := ⟨by simpa using hval.symm, hnum⟩
  have hret := hp.2
  rw [ReturnTargets.refined_quotientTarget _ _ href] at hret
  change (E (moving generators c (n+1)) - 1) / _ ∈ _
  rw [moving, map_div₀]
  exact ReturnTargets.div_prime_pow_mem_of_le _ _ _ (ReturnTargets.refined_precision_ge _ _ _ href) hret

/-- Every active branch of a permanent site is one of the actual guards or
one of the two indexed primary tails. -/
private theorem norm_branch_of_vertical (p : PrimeIndex) (b : Bool)
    (hb : MixedStageSelection.Active (permanentSite requirements p).paired b) :
    ∃ v : (Bool × ℕ ⊕ PrimeIndex), ∀ x : RatFunc ℚ, vertical v x = 1 →
      ‖(permanentSite requirements p).evaluate b hb x‖ = 1 := by
  cases b with
  | true =>
    exact ⟨.inr p, fun x hx => ConstructionReturns.norm_eq_one_of_mulValuation_eq_one _ hx⟩
  | false =>
    obtain ⟨k, rfl⟩ := (family.paired_iff p).mp (hb.resolve_left (by decide))
    refine ⟨.inl ((decode k).1, newIndex (decode k).2), fun x hx => ?_⟩
    change primaryAtStage (allocationStage (decode k).1 (newIndex (decode k).2)) x = 1 at hx
    rw [allocate_newIndex] at hx
    have he : (permanentSite requirements (family.prime k)).branch false =
        (family.atStage k).primary.val.val := by rw [family.permanent_eq]; rfl
    unfold Site.evaluate
    simp only [he]
    exact ConstructionReturns.norm_eq_one_of_mulValuation_eq_one _ hx

private theorem branch_returns_of_vertical_units (c : Bool)
    (hunit : ∀ v, ∀ᶠ n in atTop, vertical v (moving generators c n * generators (stage c (.b (n+1)))) = 1 ∧
      vertical v (generators (stage c (.q n))) = 1)
    (p : PrimeIndex) (b : Bool) (hb : MixedStageSelection.Active (permanentSite requirements p).paired b) :
    ∀ᶠ n in atTop,
      ((permanentSite requirements p).evaluate b hb (moving generators c (n+1)) - 1) /
        (p.val : ℚ_[p.val])^(n+1) ∈ PadicInt.subring p.val := by
  obtain ⟨j, rfl⟩ := primes.surjective p
  obtain ⟨v, hv⟩ := norm_branch_of_vertical (primes j) b hb
  obtain ⟨N, hN⟩ := eventually_atTop.mp (eventually_mem_indices requirements j)
  filter_upwards [hunit v, eventually_ge_atTop N] with n hn hstage
  have hproc : j ∈ (selection requirements (stage c (.q n))).batch.indices :=
    hN _ (by simp [stage]; omega)
  exact q_return_of_unit_norms c n ⟨j,hproc⟩ b hb (hv _ hn.1) (hv _ hn.2)

/-- At each fixed valuation the moving pivot eventually passes the coordinate,
so the q-ratio and its prescribed previous numerator are both units. -/
private theorem eventually_unit_at_place (c : Bool) (v : Bool × ℕ ⊕ PrimeIndex) :
    ∀ᶠ n in atTop, vertical v (moving generators c n * generators (stage c (.b (n+1)))) = 1 ∧
      vertical v (generators (stage c (.q n))) = 1 := by
  rcases v with ⟨d, j⟩ | p
  · filter_upwards [eventually_ge_atTop (j+1)] with n hn
    change primaryVal d j _ = 1 ∧ primaryVal d j _ = 1
    rw [map_mul, primary_moving, primaryVal_generator, primaryVal_generator,
      weight_b, weight_q, primaryAtomProfile_of_lt (by omega : j < 2*n)]
    simp [PrimaryWordProfiles.bWeight, PrimaryWordProfiles.qWeight,
      show j ≠ 2*n by omega, show j ≠ 2*n+1 by omega, show j ≠ 2*n+2 by omega,
      show j ≠ 2*(n+1) by omega]
  · exact Eventually.of_forall fun n => by
      change guardVal p _ = 1 ∧ guardVal p _ = 1
      simp [map_mul, guard_moving, guardVal_generator]

/-- Both actual moving families return to one modulo every positive integer
inside the same selected two-centre domain. -/
theorem eventually_moving_return (c : Bool) (m : ℕ) (hm : 0 < m) :
    ∀ᶠ n in atTop, (m : domain) ∣ movingElement c n - 1 := by
  apply eventually_dvd_of_branch_returns requirements (movingElement c) _ m hm
  exact branch_returns_of_vertical_units c (eventually_unit_at_place c)

end UnconditionalCounterexample.TwoChains
