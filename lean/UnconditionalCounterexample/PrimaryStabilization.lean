import Mathlib.Algebra.Polynomial.Degree.TrailingDegree
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.RingTheory.Valuation.Basic
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.Order.Filter.Cofinite
import Mathlib.Order.Filter.Finite
import UnconditionalCounterexample.EvaluationDVR
import Lean.Elab.Tactic.Omega

/-!
# Eventual primary valuation stabilization

For each fixed rational function, its p-adic primary values eventually equal its order
at t = 0. Every nonzero rational coefficient is a unit at all but finitely many primes
of the injective sequence. Eventually the least-degree term of a polynomial has
strictly largest multiplicative value.

The first primary argument may have additive value two. The main theorem only
requires value one at positive indices and explicitly discards the initial
index. Both evaluations and the coefficient valuations are the actual p-adic
maps; stabilization is proved, not included as a hypothesis.
-/

noncomputable section
namespace UnconditionalCounterexample.PrimaryStabilization

open Filter WithZero

/-- A fixed rational has additive valuation zero at all sufficiently late terms
of an injective natural sequence. No primality assumption is needed here. -/
theorem eventually_padicValRat_eq_zero (p : ℕ → ℕ) (hinj : Function.Injective p)
    (q : ℚ) : ∀ᶠ n in atTop, padicValRat (p n) q = 0 := by
  by_cases hq : q = 0
  · simp [hq]
  have hnumpos : 0 < q.num.natAbs := Int.natAbs_pos.mpr (Rat.num_ne_zero.mpr hq)
  filter_upwards [hinj.nat_tendsto_atTop.eventually
    (eventually_gt_atTop (max q.num.natAbs q.den))] with n hn
  have hnum : ¬p n ∣ q.num.natAbs := by
    intro hdvd
    have hle := Nat.le_of_dvd hnumpos hdvd
    omega
  have hden : ¬p n ∣ q.den := by
    intro hdvd
    have hle := Nat.le_of_dvd q.den_pos hdvd
    omega
  rw [padicValRat_def, padicValInt, padicValNat.eq_zero_of_not_dvd hnum,
    padicValNat.eq_zero_of_not_dvd hden]
  simp

/-- All nonzero coefficients of one polynomial are simultaneously units at
sufficiently late primes of an injective prime sequence. -/
theorem eventually_rational_coefficient_units (p : ℕ → ℕ)
    (hprime : ∀ n, (p n).Prime) (hinj : Function.Injective p) (f : Polynomial ℚ) :
    ∀ᶠ n in atTop, ∀ i : ℕ, f.coeff i ≠ 0 →
      @Rat.padicValuation (p n) ⟨hprime n⟩ (f.coeff i) = 1 := by
  have hevent : ∀ᶠ n in atTop, ∀ i ∈ f.support, padicValRat (p n) (f.coeff i) = 0 := by
    apply (eventually_all_finset f.support).mpr
    intro i _
    exact eventually_padicValRat_eq_zero p hinj (f.coeff i)
  filter_upwards [hevent] with n hn
  intro i hi
  simp [Rat.padicValuation, hi, hn i (Polynomial.mem_support_iff.mpr hi)]

/-- The least-degree nonzero term uniquely determines the valuation when all
nonzero coefficients are units and the argument has value strictly between zero
and one. -/
theorem valuation_eval₂_eq_pow_natTrailingDegree
    {R K Γ₀ : Type*} [CommRing R] [Field K] [LinearOrderedCommGroupWithZero Γ₀]
    (v : Valuation K Γ₀) (σ : R →+* K) (f : Polynomial R) (hf : f ≠ 0) (a : K)
    (ha0 : 0 < v a) (ha1 : v a < 1)
    (hcoeff : ∀ i : ℕ, f.coeff i ≠ 0 → v (σ (f.coeff i)) = 1) :
    v (f.eval₂ σ a) = v a ^ f.natTrailingDegree := by
  classical
  have ht := f.natTrailingDegree_mem_support_of_nonzero hf
  have htc : f.coeff f.natTrailingDegree ≠ 0 := Polynomial.mem_support_iff.mp ht
  calc
    v (f.eval₂ σ a) = v (∑ i ∈ f.support, σ (f.coeff i) * a ^ i) := by
      rw [Polynomial.eval₂_eq_sum, Polynomial.sum]
    _ = v (σ (f.coeff f.natTrailingDegree) * a ^ f.natTrailingDegree) := by
      apply v.map_sum_eq_of_lt ht
      intro i hi
      have hic : f.coeff i ≠ 0 := Polynomial.mem_support_iff.mp (Finset.mem_sdiff.mp hi).1
      have hne : i ≠ f.natTrailingDegree := by
        simpa using (Finset.mem_sdiff.mp hi).2
      have hle := f.natTrailingDegree_le_of_mem_supp i (Finset.mem_sdiff.mp hi).1
      have hlt : f.natTrailingDegree < i := by omega
      rw [map_mul, map_mul, map_pow, map_pow, hcoeff i hic,
        hcoeff f.natTrailingDegree htc, one_mul, one_mul]
      exact pow_lt_pow_right_of_lt_one₀ ha0 ha1 hlt
    _ = v a ^ f.natTrailingDegree := by
      rw [map_mul, map_pow, hcoeff f.natTrailingDegree htc, one_mul]

/-- The order at zero, written using the canonical numerator and denominator.
The valuation theorems below apply to nonzero rational functions. -/
def tOrder (f : RatFunc ℚ) : ℤ :=
  (f.num.natTrailingDegree : ℤ) - (f.denom.natTrailingDegree : ℤ)

@[simp] theorem tOrder_zero : tOrder 0 = 0 := by simp [tOrder]

@[simp] theorem tOrder_one : tOrder 1 = 0 := by simp [tOrder]

@[simp] theorem tOrder_polynomial (f : Polynomial ℚ) :
    tOrder (algebraMap (Polynomial ℚ) (RatFunc ℚ) f) = f.natTrailingDegree := by
  simp [tOrder]

@[simp] theorem tOrder_X : tOrder RatFunc.X = 1 := by
  rw [← RatFunc.algebraMap_X, tOrder_polynomial, Polynomial.natTrailingDegree_X]
  rfl

@[simp] theorem tOrder_C (q : ℚ) : tOrder (RatFunc.C q) = 0 := by
  rw [← RatFunc.algebraMap_C, tOrder_polynomial, Polynomial.natTrailingDegree_C]
  rfl

theorem tOrder_mul {f g : RatFunc ℚ} (hf : f ≠ 0) (hg : g ≠ 0) :
    tOrder (f * g) = tOrder f + tOrder g := by
  have h := congrArg Polynomial.natTrailingDegree (RatFunc.num_denom_mul f g)
  rw [Polynomial.natTrailingDegree_mul (RatFunc.num_ne_zero (mul_ne_zero hf hg))
      (mul_ne_zero f.denom_ne_zero g.denom_ne_zero),
    Polynomial.natTrailingDegree_mul f.denom_ne_zero g.denom_ne_zero,
    Polynomial.natTrailingDegree_mul (mul_ne_zero (RatFunc.num_ne_zero hf) (RatFunc.num_ne_zero hg))
      (f * g).denom_ne_zero,
    Polynomial.natTrailingDegree_mul (RatFunc.num_ne_zero hf) (RatFunc.num_ne_zero hg)] at h
  simp only [tOrder]
  omega

@[simp] theorem tOrder_inv (f : RatFunc ℚ) : tOrder f⁻¹ = -tOrder f := by
  by_cases hf : f = 0
  · simp [hf]
  have h := tOrder_mul (inv_ne_zero hf) hf
  rw [inv_mul_cancel₀ hf, tOrder_one] at h
  omega

theorem tOrder_div {f g : RatFunc ℚ} (hf : f ≠ 0) (hg : g ≠ 0) :
    tOrder (f / g) = tOrder f - tOrder g := by
  rw [div_eq_mul_inv, tOrder_mul hf (inv_ne_zero hg), tOrder_inv, sub_eq_add_neg]

/-- The polynomial calculation for an actual p-adic argument of additive value one. -/
theorem padic_aeval_eq_exp_neg_natTrailingDegree
    (p : ℕ) [Fact p.Prime] (f : Polynomial ℚ) (hf : f ≠ 0) (a : ℚ_[p])
    (ha : a.valuation = 1)
    (hcoeff : ∀ i : ℕ, f.coeff i ≠ 0 → Rat.padicValuation p (f.coeff i) = 1) :
    Padic.mulValuation (Polynomial.aeval a f) =
      WithZero.exp (-(f.natTrailingDegree : ℤ)) := by
  have hane : a ≠ 0 := by
    intro hz
    simp [hz] at ha
  have hva : Padic.mulValuation a = WithZero.exp (-1 : ℤ) := by
    simp [Padic.mulValuation, hane, ha]
  have ha0 : 0 < Padic.mulValuation a := by simp [hva]
  have ha1 : Padic.mulValuation a < 1 := by simp [hva]
  have h := valuation_eval₂_eq_pow_natTrailingDegree Padic.mulValuation
    (algebraMap ℚ (ℚ_[p])) f hf a ha0 ha1 ?_
  · change Padic.mulValuation (f.eval₂ (algebraMap ℚ (ℚ_[p])) a) = _
    rw [h, hva, ← WithZero.exp_nsmul]
    congr 1
    simp
  · intro i hi
    change Padic.mulValuation ((f.coeff i : ℚ) : ℚ_[p]) = 1
    have heq := congrArg (fun v : Valuation ℚ ℤᵐ⁰ => v (f.coeff i))
      (Padic.comap_mulValuation_eq_padicValuation (p := p))
    exact heq.trans (hcoeff i hi)

/-- Coefficient units in the numerator and denominator give the exact primary value. -/
theorem evaluationValuation_eq_exp_neg_tOrder
    (p : ℕ) [Fact p.Prime] (a : ℚ_[p]) (ha : Transcendental ℚ a)
    (hva : a.valuation = 1) (f : RatFunc ℚ) (hf : f ≠ 0)
    (hnum : ∀ i : ℕ, f.num.coeff i ≠ 0 → Rat.padicValuation p (f.num.coeff i) = 1)
    (hden : ∀ i : ℕ, f.denom.coeff i ≠ 0 → Rat.padicValuation p (f.denom.coeff i) = 1) :
    EvaluationDVR.evaluationValuation p a ha f = WithZero.exp (-tOrder f) := by
  change Padic.mulValuation (LocalEvaluation.evalAt a ha f) = _
  rw [LocalEvaluation.evalAt_apply, map_div₀,
    padic_aeval_eq_exp_neg_natTrailingDegree p f.num (RatFunc.num_ne_zero hf) a hva hnum,
    padic_aeval_eq_exp_neg_natTrailingDegree p f.denom f.denom_ne_zero a hva hden,
    ← WithZero.exp_sub]
  congr 1
  simp only [tOrder]
  omega

/-- An injective sequence of prime evaluations whose arguments have additive
value one after the first term stabilizes on every fixed nonzero rational
function. Only the explicit evaluation data are hypotheses. -/
theorem eventually_evaluationValuation_eq_exp_neg_tOrder
    (p : ℕ → ℕ) [∀ n, Fact (p n).Prime] (hinj : Function.Injective p)
    (a : ∀ n, ℚ_[p n]) (ha : ∀ n, Transcendental ℚ (a n))
    (hva : ∀ n, 0 < n → (a n).valuation = 1)
    (f : RatFunc ℚ) (hf : f ≠ 0) :
    ∀ᶠ n in atTop,
      EvaluationDVR.evaluationValuation (p n) (a n) (ha n) f = WithZero.exp (-tOrder f) := by
  filter_upwards [eventually_gt_atTop (0 : ℕ),
    eventually_rational_coefficient_units p (fun n => Fact.out) hinj f.num,
    eventually_rational_coefficient_units p (fun n => Fact.out) hinj f.denom] with n hn hnum hden
  exact evaluationValuation_eq_exp_neg_tOrder (p n) (a n) (ha n) (hva n hn) f hf hnum hden

/-- Additive primary values eventually equal the order at the horizontal point
`t=0`. The value assigned to zero by `Padic.valuation` is not used. -/
theorem eventually_evaluation_order_eq_tOrder
    (p : ℕ → ℕ) [∀ n, Fact (p n).Prime] (hinj : Function.Injective p)
    (a : ∀ n, ℚ_[p n]) (ha : ∀ n, Transcendental ℚ (a n))
    (hva : ∀ n, 0 < n → (a n).valuation = 1)
    (f : RatFunc ℚ) (hf : f ≠ 0) :
    ∀ᶠ n in atTop, (EvaluationDVR.evaluationHom (p n) (a n) (ha n) f).valuation =
      tOrder f := by
  filter_upwards [eventually_evaluationValuation_eq_exp_neg_tOrder p hinj a ha hva f hf]
    with n hn
  let e := EvaluationDVR.evaluationHom (p n) (a n) (ha n)
  have hne : e f ≠ 0 := by
    intro h
    exact hf (e.injective (h.trans (map_zero e).symm))
  change Padic.mulValuation (e f) = WithZero.exp (-tOrder f) at hn
  simp only [Padic.mulValuation_toFun, hne, ite_false] at hn
  exact neg_injective (WithZero.exp_injective hn)

end UnconditionalCounterexample.PrimaryStabilization
