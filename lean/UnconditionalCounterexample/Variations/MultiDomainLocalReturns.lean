import UnconditionalCounterexample.Variations.MultiDomainStageTargets

/-!
# Return congruences at each fixed multivariate site

The integer in the stage neighbourhood grows with the q-index. At a fixed
primary the q-column and the previous moving numerator are both units on
a tail. At guards and the extra rational point they are always units.
-/

noncomputable section
namespace UnconditionalCounterexample.Variations.MultiDomain.Targets

open NormalizedWords PrimaryWordProfiles MultivariateSelection WithZero Filter

variable {L : Type*} [Field L] (v : Valuation L ℤᵐ⁰)

def seedOrder : Option ℕ → ℤ
  | none => 0
  | some j => primaryAtomProfile 0 j

def movingOrder (n : ℕ) : Option ℕ → ℤ
  | none => 0
  | some j => primaryAtomProfile n j

theorem moving_value (P : ℕ → L) (t : L) (label : Option ℕ) (ht : v t = exp (-seedOrder label))
    (hval : ∀ i, v (P i) = exp (-(order (generator i) label : ℤ))) (n : ℕ) :
    v (moving t P n) = exp (-movingOrder n label) := by
  induction n with
  | zero => exact ht
  | succ n ih =>
    simp only [moving, map_div₀, map_mul, ih, hval, generator_stage]
    cases label with
    | none => simp [order, movingOrder]
    | some j =>
      rw [b_order, q_order, ← exp_add, ← exp_sub]
      simp only [movingOrder, AtomProfiles.primary_recurrence]
      congr 1
      ring

theorem eventually_refined (P : ℕ → L) (t : L) (label : Option ℕ) (ht : v t = exp (-seedOrder label))
    (hval : ∀ i, v (P i) = exp (-(order (generator i) label : ℤ))) :
    ∀ᶠ n in atTop, order (.q n) label = 0 ∧ v (previous t P (.q n)) = 1 := by
  cases label with
  | none => exact Filter.Eventually.of_forall (fun n ↦ by
      simp [previous, map_mul, moving_value v P t none ht hval, movingOrder, hval, order])
  | some j =>
    filter_upwards [eventually_gt_atTop j] with n hn
    have hj : j < 2*n := by omega
    simp [previous, map_mul, moving_value v P t (some j) ht hval, movingOrder, hval, order,
      primaryAtomProfile_of_lt hj, bWeight, qWeight, show j ≠ 2*n by omega, show j ≠ 2*n+1 by omega,
      show j ≠ 2*n+2 by omega, show j ≠ 2*(n+1) by omega]

/-- Any fixed site processed at all sufficiently late q-stages sees the
actual next moving element return to one to the scheduled precision. -/
theorem eventually_return (raw : ℕ → L) (t : L) (label : Option ℕ) (p : ℕ)
    (ht : v t = exp (-seedOrder label))
    (hval : ∀ i, v (RawWords.normalizedFactor raw normalizationPower i) = exp (-(order (generator i) label : ℤ)))
    (hlocal : ∀ᶠ n in atTop, let i := (Generator.q n).stage
      v ((stageValue v p label t raw i / RawWords.normalizedFactor raw normalizationPower i - 1) / (p : L)^(n+1)) ≤ 1) :
    ∀ᶠ n in atTop, v ((moving t (RawWords.normalizedFactor raw normalizationPower) n - 1) / (p : L)^n) ≤ 1 := by
  let U := RawWords.normalizedFactor raw normalizationPower
  obtain ⟨N,hN⟩ := eventually_atTop.mp ((eventually_refined v U t label ht hval).and hlocal)
  refine eventually_atTop.mpr ⟨N+1, fun k hk ↦ ?_⟩
  obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show k ≠ 0 by omega)
  obtain ⟨⟨hw,hu⟩, h⟩ := hN n (by omega)
  have href : stageValue v p label t raw (Generator.q n).stage = previous t U (.q n) := by
    unfold stageValue target
    rw [generator_stage, ite_eq_left ⟨hw,hu⟩]
  simpa only [href, previous, moving, U] using h

end UnconditionalCounterexample.Variations.MultiDomain.Targets
