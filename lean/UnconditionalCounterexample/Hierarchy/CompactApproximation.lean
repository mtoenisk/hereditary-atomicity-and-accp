import Mathlib.NumberTheory.Padics.MahlerBasis
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Topology.Separation.Profinite
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated

import UnconditionalCounterexample.GuardSupport

/-!
# Uniform polynomial approximation on compact p-adic fibres

A compact fibre's clopen value sets extend to clopens of the p-adic integers.
Mahler's expansion then supplies a finite uniform approximant. Each basis
element is a rational polynomial, and replacing its scalar coefficient by a
nearby rational preserves the required uniform precision.
-/

noncomputable section
namespace UnconditionalCounterexample.Hierarchy
open Set

/-- A clopen subset of a compact subspace of a profinite space extends to an
ambient clopen subset with exactly the specified trace. -/
private theorem clopen_trace {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [TotallyDisconnectedSpace X] {E : Set X} (hE : IsCompact E) {V : Set E} (hV : IsClopen V) :
    ∃ U : Set X, IsClopen U ∧ ∀ x : E, (x : X) ∈ U ↔ x ∈ V := by
  let incl : E → X := Subtype.val
  have hclosed := hE.isClosed.isClosedMap_subtype_val
  have hdis : incl '' V ⊆ (incl '' Vᶜ)ᶜ := by
    rintro _ ⟨x,hx,rfl⟩ ⟨y,hy,he⟩
    exact hy ((show y = x from Subtype.ext he) ▸ hx)
  obtain ⟨U,hU,h1,h2⟩ := exists_clopen_of_closed_subset_open (hclosed _ hV.isClosed)
    (hclosed _ hV.compl.isClosed).isOpen_compl hdis
  refine ⟨U,hU,fun x ↦ ⟨fun hx ↦ ?_, fun hx ↦ h1 ⟨x,hx,rfl⟩⟩⟩
  by_contra hn
  exact h2 hx ⟨x,hn,rfl⟩

/-- A locally constant function on a compact subset of a profinite space has
a continuous extension. The extension is a finite sum of clopen indicators. -/
theorem exists_continuous_extension {X Y : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [TotallyDisconnectedSpace X] [AddCommMonoid Y] [TopologicalSpace Y] [ContinuousAdd Y]
    (E : Set X) (hE : IsCompact E) (f : LocallyConstant E Y) :
    ∃ g : C(X, Y), ∀ x : E, g x = f x := by
  classical
  let : CompactSpace E := isCompact_iff_compactSpace.mp hE
  choose U hc hu using fun y : Y ↦ clopen_trace hE (f.isLocallyConstant.isClopen_fiber y)
  let F (y : Y) : C(X,Y) := ⟨(U y).indicator (fun _ ↦ y), (hc y).continuous_indicator continuous_const⟩
  refine ⟨∑ y ∈ f.range_finite.toFinset, F y, fun x ↦ ?_⟩
  simp only [ContinuousMap.sum_apply]
  rw [Finset.sum_eq_single (f x)]
  · change (U (f x)).indicator (fun _ ↦ f x) (x : X) = _
    exact Set.indicator_of_mem ((hu (f x) x).mpr rfl) _
  · intro y _ hy
    change (U y).indicator (fun _ ↦ y) (x : X) = 0
    exact Set.indicator_of_notMem (fun h ↦ hy ((hu _ x).mp h).symm) _
  · intro hm
    exact (hm (f.range_finite.mem_toFinset.mpr (Set.mem_range_self x))).elim

open Polynomial Filter Finset
open scoped Polynomial Topology fwdDiff

variable {p : ℕ} [Fact p.Prime]

/-- The rational polynomial representing the n-th Mahler basis function. -/
def mahlerPolynomial (n : ℕ) : ℚ[X] := descPochhammer ℚ n * C (n.factorial : ℚ)⁻¹

theorem aeval_mahlerPolynomial (n : ℕ) (x : ℤ_[p]) :
    aeval (x : ℚ_[p]) (mahlerPolynomial n) = (mahler n x : ℚ_[p]) := by
  induction x using isClosed_property (PadicInt.denseRange_natCast (p := p))
  · apply isClosed_eq
    · exact (mahlerPolynomial n).continuous_aeval.comp (by fun_prop)
    · fun_prop
  · rename_i m
    simp only [mahlerPolynomial, map_mul, aeval_C, eq_ratCast, Rat.cast_inv,
      Rat.cast_natCast, mahler_natCast_eq, PadicInt.coe_natCast]
    rw [Nat.cast_choose_eq_descPochhammer_div, div_eq_mul_inv]
    congr 1
    rw [aeval_def, ← eval_map, descPochhammer_map]

local instance : IsBoundedSMul ℤ_[p] ℚ_[p] :=
  .of_norm_smul_le fun a x ↦ by
    change ‖(a : ℚ_[p]) * x‖ ≤ ‖a‖ * ‖x‖
    rw [norm_mul]
    rfl

private theorem hasSum_approx (f : C(ℤ_[p], ℚ_[p])) (ε : ℝ) (hε : 0 < ε) :
    ∃ s : Finset ℕ, ∀ x : ℤ_[p], ‖(∑ i ∈ s, (mahler i x : ℚ_[p]) * (Δ_[1]^[i] f 0)) - f x‖ < ε := by
  have h := (PadicInt.hasSum_mahler f).eventually (Metric.ball_mem_nhds f hε)
  obtain ⟨s, hs⟩ := h.exists
  refine ⟨s, fun x ↦ ?_⟩
  have hnorm := ContinuousMap.norm_coe_le_norm ((∑ i ∈ s, PadicInt.mahlerTerm (Δ_[1]^[i] f 0) i) - f) x
  apply lt_of_le_of_lt _ (Metric.mem_ball.mp hs)
  simpa only [dist_eq_norm_sub, ContinuousMap.sub_apply, ContinuousMap.sum_apply,
    PadicInt.mahlerTerm_apply, Algebra.smul_def, PadicInt.algebraMap_apply] using hnorm

/-- Rational polynomials approximate continuous p-adic functions uniformly on the p-adic integers. -/
theorem exists_rational_polynomial_approx_full (f : C(ℤ_[p], ℚ_[p])) (ε : ℝ) (hε : 0 < ε) :
    ∃ F : ℚ[X], ∀ x : ℤ_[p], ‖aeval (x : ℚ_[p]) F - f x‖ < ε := by
  classical
  obtain ⟨s, hs⟩ := hasSum_approx f (ε/2) (half_pos hε)
  let a (i : ℕ) : ℚ_[p] := Δ_[1]^[i] f 0
  choose b hb using fun i ↦ (Padic.denseRange_ratCast p).exists_dist_lt (a i) (half_pos hε)
  refine ⟨∑ i ∈ s, mahlerPolynomial i * C (b i), fun x ↦ ?_⟩
  let g (i : ℕ) : ℚ_[p] := mahler i x
  have hsum : ‖∑ i ∈ s, g i * ((b i : ℚ_[p]) - a i)‖ ≤ ε/2 := by
    apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (half_pos hε).le
    intro i _
    rw [norm_mul]
    apply (mul_le_of_le_one_left (norm_nonneg _) (mahler i x).norm_le_one).trans
    exact (by simpa only [dist_eq_norm_sub, norm_sub_rev] using (hb i).le)
  simp only [map_sum, map_mul, aeval_C, aeval_mahlerPolynomial]
  change ‖(∑ i ∈ s, g i * (b i : ℚ_[p])) - f x‖ < ε
  calc
    _ ≤ ‖(∑ i ∈ s, g i * (b i : ℚ_[p])) - ∑ i ∈ s, g i * a i‖ +
          ‖(∑ i ∈ s, g i * a i) - f x‖ := norm_sub_le_norm_sub_add_norm_sub ..
    _ < ε/2 + ε/2 := add_lt_add_of_le_of_lt (by simpa only [mul_sub, sum_sub_distrib] using hsum) (hs x)
    _ = ε := add_halves _

/-- Uniform rational polynomial approximation of locally constant data on any
compact subset of the p-adic integers, with arbitrary p-adic target values. -/
theorem exists_rational_polynomial_approx (p : ℕ) [Fact p.Prime] (E : Set ℤ_[p])
    (hE : IsCompact E) (f : LocallyConstant E ℚ_[p]) (ε : ℝ) (hε : 0 < ε) :
    ∃ F : ℚ[X], ∀ x : E, ‖aeval (x.val : ℚ_[p]) F - f x‖ < ε := by
  obtain ⟨g,hg⟩ := exists_continuous_extension E hE f
  obtain ⟨F,hF⟩ := exists_rational_polynomial_approx_full g ε hε
  exact ⟨F, fun x ↦ hg x ▸ hF x⟩

/-- Evaluation-ring version indexed by a rational prime. -/
theorem exists_polynomial_approx (p : GuardSupport.PrimeIndex) (E : Set ℤ_[p.val])
    (hE : IsCompact E) (f : LocallyConstant E ℚ_[p.val]) {ε : ℝ} (hε : 0 < ε) :
    ∃ F : ℚ[X], ∀ x : E, ‖F.eval₂ (Rat.castHom ℚ_[p.val]) (x.val : ℚ_[p.val]) - f x‖ < ε :=
  exists_rational_polynomial_approx p.val E hE f ε hε

end UnconditionalCounterexample.Hierarchy
