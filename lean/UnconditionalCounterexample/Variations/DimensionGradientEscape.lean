import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Tactic.Linarith

/-!
# Escape of the scheduled multivariate gradient

The weights of the scheduled polynomial distinguish the first generator detected by a given
nonzero linear functional. A nonzero polynomial evaluated at powers of a
uniformizer decays at a rate controlled by its multiplicity at zero. The
quadratic precision in the schedule is faster than any such rate.
-/

namespace UnconditionalCounterexample.Variations

open Filter Polynomial
open scoped Topology

variable {K : Type*} [NontriviallyNormedField K]

/-- On an unbounded set of stages, a nonzero polynomial in `π^i` cannot decay
as fast as a constant times `‖π‖^(i²)`. -/
theorem polynomial_eq_zero_of_quadratic_decay (π : K) (hπ : π ≠ 0) (hsmall : ‖π‖ < 1)
    (P : K[X]) (C : ℝ) (hC : 0 ≤ C)
    (hfast : ∀ n : ℕ, ∃ i ≥ n, ‖P.eval (π^i)‖ ≤ C * ‖π‖^(i*i)) : P = 0 := by
  by_contra hn
  obtain ⟨Q, hPQ, hndvd⟩ := P.exists_eq_pow_rootMultiplicity_mul_and_not_dvd hn 0
  let k := P.rootMultiplicity 0
  have hP : P = X^k * Q := by simpa [k] using hPQ
  have hnQ : Q.eval 0 ≠ 0 := fun h ↦ hndvd ((dvd_iff_isRoot).mpr h)
  let ε := ‖Q.eval 0‖ / 2
  have hε : 0 < ε := half_pos (norm_pos_iff.mpr hnQ)
  have hpow := tendsto_pow_atTop_nhds_zero_of_norm_lt_one hsmall
  have hQ : ∀ᶠ i : ℕ in atTop, ε < ‖Q.eval (π^i)‖ :=
    ((Q.continuous.tendsto 0).comp hpow).norm.eventually_const_lt (half_lt_self (norm_pos_iff.mpr hnQ))
  have hreal : Tendsto (fun i : ℕ ↦ C * ‖π‖^i) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg π) hsmall).const_mul C
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hQ.and (hreal.eventually_lt_const hε))
  obtain ⟨i, hi, hf⟩ := hfast (max N (k+1))
  obtain ⟨hlo, hhi⟩ := hN i (le_trans (le_max_left ..) hi)
  have hi' : k+1 ≤ i := le_trans (le_max_right ..) hi
  have hexp : i*k+i ≤ i*i := by simpa [Nat.mul_add] using Nat.mul_le_mul_left i hi'
  have hq : ‖π‖^(i*k) * ‖Q.eval (π^i)‖ ≤ ‖π‖^(i*k) * (C * ‖π‖^i) := calc
    _ = ‖P.eval (π^i)‖ := by rw [hP]; simp [pow_mul]
    _ ≤ C * ‖π‖^(i*i) := hf
    _ ≤ C * ‖π‖^(i*k+i) :=
      mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one (norm_nonneg π) hsmall.le hexp) hC
    _ = _ := by rw [pow_add]; ring
  exact (hhi.trans hlo).not_ge (le_of_mul_le_mul_left hq (pow_pos (norm_pos_iff.mpr hπ) _))

/-- Normalized scalar jets close to a nonzero scheduling polynomial force the
original jet norms to diverge along every sequence of stages tending to infinity. -/
theorem norm_tendsto_atTop_of_scheduled_direction (π : K) (hπ : π ≠ 0) (hsmall : ‖π‖ < 1)
    (P : K[X]) (hP : P ≠ 0) (s : ℕ → ℕ) (hs : Tendsto s atTop atTop)
    (w α : ℕ → K) (C : ℝ) (hC : 0 ≤ C)
    (hscale : ∀ᶠ n in atTop, ‖(α n)⁻¹‖ ≤ ‖π‖^(s n * s n))
    (happrox : ∀ᶠ n in atTop, ‖(α n)⁻¹ * w n - P.eval (π^(s n))‖ ≤ C * ‖π‖^(s n * s n)) :
    Tendsto (fun n ↦ ‖w n‖) atTop atTop := by
  rw [Filter.tendsto_atTop]
  intro R
  by_contra hn
  apply hP
  apply polynomial_eq_zero_of_quadratic_decay π hπ hsmall P (max R 0 + C) (by positivity)
  intro m
  obtain ⟨N, hN⟩ := eventually_atTop.mp ((hs.eventually_ge_atTop m).and (hscale.and happrox))
  rw [eventually_atTop] at hn
  push Not at hn
  obtain ⟨n, hnN, hnR⟩ := hn N
  obtain ⟨hnm, hα, herr⟩ := hN n hnN
  refine ⟨s n, hnm, ?_⟩
  have hw : ‖(α n)⁻¹ * w n‖ ≤ max R 0 * ‖π‖^(s n * s n) := by
    rw [norm_mul, mul_comm]
    exact mul_le_mul (hnR.le.trans (le_max_left ..)) hα (norm_nonneg _) (le_max_right ..)
  calc
    ‖P.eval (π^(s n))‖ ≤ ‖(α n)⁻¹ * w n‖ + ‖(α n)⁻¹ * w n - P.eval (π^(s n))‖ := by
      simpa using norm_sub_le ((α n)⁻¹ * w n) ((α n)⁻¹ * w n - P.eval (π^(s n)))
    _ ≤ _ := by rw [add_mul]; exact add_le_add hw herr

/-- When the scheduled generator gradients span, every nonzero linear functional
of the word gradient escapes. The prime may enter the schedule after any finite prefix. -/
theorem gradient_direction_tendsto_atTop {V : Type*} [NormedAddCommGroup V] [NormedSpace K V]
    {m : ℕ} (g : Fin m → V) (hspan : Submodule.span K (Set.range g) = ⊤)
    (π : K) (hπ : π ≠ 0) (hsmall : ‖π‖ < 1) (s : ℕ → ℕ) (hs : Tendsto s atTop atTop)
    (w : ℕ → V) (α : ℕ → K) (hscale : ∀ᶠ n in atTop, ‖(α n)⁻¹‖ ≤ ‖π‖^(s n * s n))
    (hgrad : ∀ᶠ n in atTop, ‖(α n)⁻¹ • w n - ∑ j : Fin m, (π^(s n))^(j : ℕ) • g j‖ ≤
      ‖π‖^(s n * s n)) (L : V →L[K] K) (hL : L ≠ 0) :
    Tendsto (fun n ↦ ‖L (w n)‖) atTop atTop := by
  classical
  let P : K[X] := ∑ j : Fin m, monomial (j : ℕ) (L (g j))
  have hP : P ≠ 0 := by
    intro he
    apply hL
    have hcoeff (j : Fin m) : L (g j) = 0 := by
      have h := congrArg (fun p : K[X] ↦ p.coeff j) he
      simpa [P, finsetSum_coeff, coeff_monomial, Fin.val_inj] using h
    have hker : Submodule.span K (Set.range g) ≤ LinearMap.ker L.toLinearMap := by
      apply Submodule.span_le.mpr
      rintro _ ⟨j, rfl⟩
      exact hcoeff j
    ext x
    exact hker (hspan ▸ Submodule.mem_top)
  apply norm_tendsto_atTop_of_scheduled_direction π hπ hsmall P hP s hs (fun n ↦ L (w n)) α
    ‖L‖ (norm_nonneg _) hscale
  filter_upwards [hgrad] with n hn
  have hb := (L.le_opNorm ((α n)⁻¹ • w n - ∑ j : Fin m, (π^(s n))^(j : ℕ) • g j)).trans
    (mul_le_mul_of_nonneg_left hn (norm_nonneg _))
  simpa [P, eval_finsetSum, eval_monomial, mul_comm] using hb

end UnconditionalCounterexample.Variations
