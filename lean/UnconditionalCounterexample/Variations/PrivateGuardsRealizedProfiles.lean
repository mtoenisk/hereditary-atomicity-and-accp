import UnconditionalCounterexample.Variations.PrivateGuardsProcessed
import UnconditionalCounterexample.Variations.PrivateGuardsBornUnits
import UnconditionalCounterexample.Variations.PrivateGuardsMovingReturns
import UnconditionalCounterexample.Variations.PrivateGuardsMoving

/-! # Unconditional profiles and returns of the punctured construction -/

noncomputable section
namespace UnconditionalCounterexample.Variations.PrivateGuards.Live

open GuardSupport MvPolynomial MultivariateSelection MultiDomain WithZero Filter NormalizedWords

variable {r d : ℕ} {K : Type*} [Field K] [CharZero K]
  (P : TablePolicy r K) (q : PrimeIndex) (c : Fin (r+1) → ℚ) (C : Config r d)

local notation "liveRule" => tableRule P q c
local notation "T" => publicPath P q c C
local notation "B" => family C liveRule

abbrev publicPrimary (j : ℕ) := ((T).places.primary j).valuation
abbrev publicGuard (p : PrimeIndex) := ((T).places.guard p).valuation

local notation "π" => publicPrimary P q c C
local notation "γ" => publicGuard P q c C

private theorem evaluation_eq {E : Type*} [Field E] [Algebra ℚ E] (x : Fin (r+1) → E)
    (hx : AlgebraicIndependent ℚ x) (f : Poly r) :
    IndependentTuples.evaluation x hx (algebraMap (Poly r) (FunctionField (r+1)) f) = (aeval x).toRingHom f :=
  IsFractionRing.lift_algebraMap (K := FunctionField (r+1)) (g := (aeval x : Poly r →ₐ[ℚ] E).toRingHom) hx f

theorem mixed_primary_profile (j n : ℕ) :
    π j ((B).generator mixedPower n) = exp (-(Targets.order (Targets.generator n) (some j) : ℤ)) := by
  by_cases hn : j/2 ≤ n
  · let t := (T).places.primary j
    exact (evaluated_evidence C liveRule _ _ (evaluation_eq t.x t.independent) Padic.mulValuation
      ((T).places.primes j).val (EvaluationDVR.valuation_prime _ (RingHom.id _)) (some j) n
      (processed_primary_mem P q c C j n hn)).1
  · rw [Targets.order_zero_later_birth n j (by omega)]
    simpa only [Nat.cast_zero,neg_zero,exp_zero] using primary_unborn_generator P q c C j n (by omega)

theorem mixed_guard_profile (p : PrimeIndex) (n : ℕ) : γ p ((B).generator mixedPower n) = 1 := by
  by_cases hp : p ∈ ((T).batch n).processed
  · let t := (T).places.guard p
    have h := (evaluated_evidence C liveRule _ _ (evaluation_eq t.x t.independent) ((T).places.guardVal p)
      p.val ((T).places.guard_prime p) none n (processed_guard_mem P q c C p n hp)).1
    exact h.trans (by simp [Targets.order])
  · exact guard_unprocessed_generator P q c C hp

theorem public_seed (j : ℕ) : π j (coordinate 0) = exp (-Targets.seedOrder (some j)) := by
  change ((T).primaryBirth j).tuple.valuation (coordinate 0) = _
  rw [((T).primaryBirth j).order]
  simp [Targets.seedOrder,firstOrder,primaryAtomProfile]

theorem guard_seed (p : PrimeIndex) : γ p (coordinate 0) = 1 := by
  let g := ((T).permanentFibre p).guard
  have h : g.avoids (map (Int.castRingHom (ZMod p.val)) (X 0 : IntPolys (r+1))) := by
    simp only [ScreenedGuard.avoids,map_X,aeval_X]
    exact fun he => g.outside ⟨0,(map_zero _).trans he.symm⟩
  change g.tuple.valuation (coordinate 0) = 1
  simpa only [coordinate,rationalize,map_X] using g.unit_of_avoids (X 0) h

theorem actualMovingValues : MovingValues C liveRule π γ where
  seed i := by
    rcases i with (j | p) | ⟨k,b⟩
    · exact public_seed P q c C j
    · exact (guard_seed P q c C p).trans (by simp [branchLabel,Targets.seedOrder])
    · have h := (event C liveRule k).pair.tests_are_units (seed_mem C liveRule k)
      cases b
      · exact h.1.trans (by simp [branchLabel,Targets.seedOrder])
      · exact h.2.trans (by simp [branchLabel,Targets.seedOrder])
  generator i n := by
    rcases i with (j | p) | ⟨k,b⟩
    · exact mixed_primary_profile P q c C j n
    · exact (mixed_guard_profile P q c C p n).trans (by simp [branchLabel,Targets.order])
    · have h := generator_units C liveRule k n
      cases b
      · exact h.1.trans (by simp [branchLabel,Targets.order])
      · exact h.2.trans (by simp [branchLabel,Targets.order])

private theorem processed_after (j n : ℕ) (hj : j < n) : j < (Generator.q n).stage := by
  simp [Generator.stage]
  omega

/-- Every vertical branch sees the moving elements approach one with the
prescribed growing precision, including both private rational evaluations. -/
theorem actualBranchReturn (i : Branch) :
    ∀ᶠ n in atTop, branchVal C liveRule π γ i
      ((movingValue C liveRule n - 1) / ((branchPrime C liveRule (T).places.primes i).val : FunctionField (r+1))^n) ≤ 1 := by
  let V := actualMovingValues P q c C
  rcases i with (j | p) | ⟨k,b⟩
  · let t := (T).places.primary j
    apply field_moving_return C liveRule _ _ (evaluation_eq t.x t.independent) Padic.mulValuation _
      (EvaluationDVR.valuation_prime _ (RingHom.id _)) (some j) (V.seed (.inl (.inl j))) (V.generator (.inl (.inl j)))
    filter_upwards [eventually_gt_atTop (j/2)] with n hn
    exact processed_primary_mem P q c C j _ (processed_after _ _ hn).le
  · let t := (T).places.guard p
    apply field_moving_return C liveRule _ _ (evaluation_eq t.x t.independent) ((T).places.guardVal p)
      p.val ((T).places.guard_prime p) none (V.seed (.inl (.inr p))) (V.generator (.inl (.inr p)))
    filter_upwards [eventually_gt_atTop ((T).firstAppearance p)] with n hn
    exact processed_guard_mem P q c C p _ ((T).eventual_processed p (processed_after _ _ hn))
  · let s := (event C liveRule k).pair
    let p := prime C liveRule k
    let v := Padic.mulValuation (p := p.val)
    let ψ := IndependentTuples.evaluation (s.point b) (s.point_independent b)
    have he : branchVal C liveRule π γ (.inr (k,b)) = v.comap ψ := by cases b <;> rfl
    have hseed := V.seed (.inr (k,b))
    have hg := V.generator (.inr (k,b))
    rw [he] at hseed hg ⊢
    apply field_moving_return C liveRule _ _ (evaluation_eq (s.point b) (s.point_independent b)) v p.val
      (EvaluationDVR.valuation_prime _ (RingHom.id _)) none hseed hg
    filter_upwards [eventually_gt_atTop k] with n hn
    exact processed_private_mem P q c C (processed_after _ _ hn) b

end UnconditionalCounterexample.Variations.PrivateGuards.Live
