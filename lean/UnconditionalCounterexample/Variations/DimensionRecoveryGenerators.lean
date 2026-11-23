import UnconditionalCounterexample.Variations.DimensionCoefficientTransfer
import UnconditionalCounterexample.Variations.DimensionGradientEscape
import Mathlib.RingTheory.MvPolynomial.Basic

noncomputable section
namespace UnconditionalCounterexample.Variations

open MvPolynomial Filter
open scoped Topology

variable {K σ ι : Type*} [NontriviallyNormedField K] [Fintype σ]
variable {E : ι → Type*} [∀ i, NontriviallyNormedField (E i)] [∀ i, NormedAlgebra K (E i)]

/-- Finite generators frozen with the p-adic family, before any stage or subring is chosen. -/
structure RecoveryGenerators (u : ∀ i, σ → E i) where
  count : ℕ
  gen : Fin count → MvPolynomial σ K
  span : Ideal.span (Set.range gen) = ⨅ i, RingHom.ker (aeval (R := K) (u i)).toRingHom

def recoveryGenerators (u : ∀ i, σ → E i) : RecoveryGenerators (K := K) u := by
  let I := ⨅ i, RingHom.ker (aeval (R := K) (u i)).toRingHom
  let h := Submodule.fg_iff_exists_fin_generating_family.mp (IsNoetherian.noetherian I)
  exact ⟨h.choose, h.choose_spec.choose, h.choose_spec.choose_spec⟩

theorem exists_scaledCoefficient_bound {τ : Type*} [Finite τ] (π : K) (hπ : ‖π‖ < 1)
    (s : ℕ) (W : τ → MvPolynomial σ K) :
    ∃ c : ℕ, ∀ j m, ‖scaledCoefficient (π^s) (π^c) m (W j)‖ ≤ 1 := by
  classical
  let T := (j : τ) × (W j).support
  have hev (v : T) : ∀ᶠ c : ℕ in atTop,
      ‖π^c * scaledCoefficient (π^s) 1 v.2.val (W v.1)‖ ≤ 1 := by
    apply Filter.Eventually.mono _ fun _ h ↦ le_of_lt h
    apply Filter.Tendsto.eventually_lt_const (show (0:ℝ)<1 by norm_num)
    simpa using ((tendsto_pow_atTop_nhds_zero_of_norm_lt_one hπ).mul_const
      (scaledCoefficient (π^s) 1 v.2.val (W v.1))).norm
  obtain ⟨c,hc⟩ := (eventually_all.mpr hev).exists
  refine ⟨c,fun j m ↦ ?_⟩
  by_cases h : m ∈ (W j).support
  · simpa [scaledCoefficient, div_eq_mul_inv, mul_assoc] using hc ⟨j, m, h⟩
  · simp [scaledCoefficient, notMem_support_iff.mp h]

namespace RecoveryGenerators

variable {u : ∀ i, σ → E i} (G : RecoveryGenerators (K := K) u)

def direction (π : K) (n : ℕ) := ∑ j : Fin G.count, (π^n)^j.val • G.gen j

omit [Fintype σ] in
theorem direction_vanish (π : K) (n : ℕ) (i : ι) : aeval (u i) (G.direction π n) = 0 := by
  have h (j : Fin G.count) : aeval (u i) (G.gen j) = 0 :=
    Ideal.mem_iInf.mp (G.span ▸ (Ideal.subset_span (Set.mem_range_self j))) i
  simp [direction, h]

omit [Fintype σ] in
theorem direction_gradient (π : K) (n : ℕ) (i : ι) :
    (fun l ↦ aeval (u i) (pderiv l (G.direction π n))) =
    ∑ j : Fin G.count, (algebraMap K (E i) π ^ n)^j.val • (fun l ↦ aeval (u i) (pderiv l (G.gen j))) := by
  ext l
  simp [direction, Finset.sum_apply, Algebra.smul_def]

end RecoveryGenerators
end UnconditionalCounterexample.Variations
