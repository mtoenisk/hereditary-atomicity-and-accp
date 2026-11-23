import UnconditionalCounterexample.Variations.UnivariateCentres
import UnconditionalCounterexample.ReturnTargets

/-!
# The two initial return elements for the two-centre construction

The dyadic condition on the guard is essential for the translated seed. At
odd primes only the reduction modulo the prime enters its unit tests.
-/

noncomputable section
namespace UnconditionalCounterexample.TwoChains

open GuardSupport
local instance : Algebra ℚ (RatFunc ℚ) := RatFunc.instAlgebraOfPolynomial ℚ ℚ

/-- The second seed uses the dyadic normalization in the manuscript. -/
def seed : Bool → RatFunc ℚ
  | false => RatFunc.X
  | true => (RatFunc.X - 1) / 2

theorem seed_ne_zero (c : Bool) : seed c ≠ 0 := by
  cases c
  · exact RatFunc.X_ne_zero
  · apply div_ne_zero _ (by norm_num)
    apply sub_ne_zero.mpr
    intro h
    exact (RatFunc.transcendental_X (K := ℚ)) (h ▸ isIntegral_one).isAlgebraic

/-- Rational functions evaluated at the primary and guard arguments. -/
def seedValue {p : ℕ} [Fact p.Prime] (x : ℚ_[p]) : Bool → ℚ_[p]
  | false => x
  | true => (x - 1) / 2

theorem eval_seed {p : ℕ} [Fact p.Prime] (x : ℚ_[p]) (hx : Transcendental ℚ x)
    (c : Bool) : EvaluationDVR.evaluationHom p x hx (seed c) = seedValue x c := by
  have hX : EvaluationDVR.evaluationHom p x hx RatFunc.X = x := by
    change LocalEvaluation.evalAt x hx RatFunc.X = x
    exact LocalEvaluation.evalAt_X _ _
  cases c <;> simp [seed, seedValue, map_div₀, hX, map_ofNat]

/-- At the dyadic guard both seeds are units, even though the second seed
involves division by two. -/
theorem dyadic_seed_norm (β : ℤ_[2]) (hβ : PadicInt.toZModPow 2 β = 3)
    (c : Bool) : ‖seedValue β.val c‖ = 1 := by
  have hker : β - 3 ∈ RingHom.ker (PadicInt.toZModPow 2 : ℤ_[2] →+* _) := by
    rw [RingHom.mem_ker, map_sub, map_ofNat, hβ, sub_self]
  rw [PadicInt.ker_toZModPow, Ideal.mem_span_singleton] at hker
  obtain ⟨u, hu⟩ := hker
  have heq : β = 3 + (2 : ℤ_[2]) ^ 2 * u := by linear_combination hu
  cases c
  · have hunit : IsUnit β := by
      apply (padicInt_isUnit_iff_toZMod_ne_zero _).mpr
      rw [heq, map_add, map_mul, map_pow, map_ofNat, map_ofNat]
      rw [show (2 : ZMod 2) = 0 by decide]
      norm_num
      decide
    exact PadicInt.isUnit_iff.mp hunit
  · let w : ℤ_[2] := 1 + 2*u
    have hw : IsUnit w := by
      apply (padicInt_isUnit_iff_toZMod_ne_zero _).mpr
      simp only [w, map_add, map_one, map_mul, map_ofNat, show (2 : ZMod 2) = 0 by decide,
        zero_mul, add_zero]
      decide
    have hv : seedValue β.val true = w.val := by
      change (β.val - 1) / 2 = w.val
      rw [heq]
      push_cast
      change _ = ((1 + 2 * u : ℤ_[2]) : ℚ_[2])
      push_cast
      change (3 + (2 : ℚ_[2])^2 * u.val - 1)/2 = 1 + 2*u.val
      ring
    rw [hv]
    exact PadicInt.isUnit_iff.mp hw

private theorem odd_norm_two {p : ℕ} [Fact p.Prime] (hp : 2 < p) :
    ‖(2 : ℚ_[p])‖ = 1 := by
  have hcop : Nat.Coprime p 2 := (Fact.out : p.Prime).coprime_iff_not_dvd.mpr
    (fun h => (not_le_of_gt hp) (Nat.le_of_dvd (by decide) h))
  simpa using Padic.norm_natCast_eq_one_iff.mpr hcop

/-- Both seeds are units at every odd guard whose residue avoids the centres. -/
theorem odd_guard_seed_norm {p : ℕ} [Fact p.Prime] (hp : 2 < p) (β : ℤ_[p])
    (h₀ : PadicInt.toZMod β ≠ 0) (h₁ : PadicInt.toZMod β ≠ 1) (c : Bool) :
    ‖seedValue β.val c‖ = 1 := by
  cases c
  · exact PadicInt.isUnit_iff.mp ((padicInt_isUnit_iff_toZMod_ne_zero _).mpr h₀)
  · have hu : IsUnit (β - 1) := (padicInt_isUnit_iff_toZMod_ne_zero _).mpr (by
      simpa only [map_sub, map_one, sub_ne_zero] using h₁)
    change ‖(β.val - 1) / 2‖ = 1
    rw [norm_div, odd_norm_two hp, div_one]
    exact PadicInt.isUnit_iff.mp hu

/-- At an odd primary the distinguished seed has precisely the displacement
order, and the seed of the other colour is a unit. -/
theorem primary_seed_norm {p : ℕ} [Fact p.Prime] (hp : 2 < p) (α : ℤ_[p])
    (c : Bool) (k : ℕ) (ht : Transcendental ℚ α.val)
    (hr : PadicInt.toZMod α = if c then 1 else 0)
    (hk : (α.val - (if c then 1 else 0)).valuation = k) :
    ‖seedValue α.val c‖ = (p : ℝ)^(-(k : ℤ)) ∧ ‖seedValue α.val (!c)‖ = 1 := by
  cases c
  · simp only [Bool.false_eq_true, ite_false, sub_zero] at hr hk
    have hu : IsUnit (α - 1) := (padicInt_isUnit_iff_toZMod_ne_zero _).mpr (by simp [hr])
    refine ⟨(Padic.norm_eq_zpow_neg_valuation ht.ne_zero).trans (by rw [hk]), ?_⟩
    change ‖(α.val - 1)/2‖ = 1
    rw [norm_div, odd_norm_two hp, div_one]
    exact PadicInt.isUnit_iff.mp hu
  · simp only [ite_true] at hr hk
    have hu : IsUnit α := (padicInt_isUnit_iff_toZMod_ne_zero _).mpr (by simp [hr])
    have hn : α.val - 1 ≠ 0 := sub_ne_zero.mpr (fun h =>
      ht (h ▸ isIntegral_one).isAlgebraic)
    refine ⟨?_, PadicInt.isUnit_iff.mp hu⟩
    change ‖(α.val - 1)/2‖ = _
    rw [norm_div, odd_norm_two hp, div_one, Padic.norm_eq_zpow_neg_valuation hn, hk]

end UnconditionalCounterexample.TwoChains
