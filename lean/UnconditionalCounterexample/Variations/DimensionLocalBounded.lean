import UnconditionalCounterexample.RadicalConductor
import Mathlib.Analysis.Normed.Module.Seminorm.Norm
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Tactic.Linarith
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Boundedness modulo the full conductor

In the finite-dimensional conductor quotient, the image of the
integral subring is closed because it contains a lattice. If it were unbounded,
compactness of a closed ball would give an entire nonzero scalar line in the
image. Clearing one denominator at a time then puts the generated ambient ideal
in the image, contradicting the definition of the conductor.
-/

namespace UnconditionalCounterexample.Variations

open Filter Topology

/-- A closed integral-scalar-stable set containing vectors of arbitrarily large norm
contains a whole nonzero scalar line when its ambient space has compact closed balls. -/
theorem exists_line_of_unbounded {K E : Type*} [NontriviallyNormedField K]
    [NormedAddCommGroup E] [NormedSpace K E] [ProperSpace E]
    (C : Set E) (hclosed : IsClosed C)
    (hstable : ∀ (b : K), ‖b‖ ≤ 1 → ∀ x ∈ C, b • x ∈ C)
    (hunbounded : ∀ R : ℝ, ∃ x ∈ C, R < ‖x‖) :
    ∃ v : E, v ≠ 0 ∧ ∀ a : K, a • v ∈ C := by
  obtain ⟨c, hc⟩ := NormedField.exists_one_lt_norm K
  choose x hx hnorm using fun n : ℕ ↦ hunbounded (n + 1)
  have hne (n : ℕ) : x n ≠ 0 := by
    intro h
    have := hnorm n
    rw [h, norm_zero] at this
    linarith [Nat.cast_nonneg (α := ℝ) n]
  choose b _ hbupper hblower _ using fun n ↦ rescale_to_shell hc zero_lt_one (hne n)
  let y (n : ℕ) := b n • x n
  have hy (n : ℕ) : y n ∈ Metric.closedBall 0 1 := by
    simpa [Metric.mem_closedBall, dist_zero_right, y] using (hbupper n).le
  obtain ⟨v, _, φ, hφ, hv⟩ := (isCompact_closedBall (0 : E) 1).tendsto_subseq hy
  have hl : 1 / ‖c‖ ≤ ‖v‖ := ge_of_tendsto' hv.norm (fun n ↦ hblower (φ n))
  refine ⟨v, (norm_pos_iff.mp ((div_pos zero_lt_one (by linarith)).trans_le hl)), fun a ↦ ?_⟩
  apply hclosed.mem_of_tendsto (hv.const_smul a)
  obtain ⟨N, hN⟩ := exists_nat_gt ‖a‖
  filter_upwards [eventually_ge_atTop N] with n hn
  have ha : ‖a‖ ≤ ‖x (φ n)‖ := by
    have hge : (N : ℝ) ≤ (φ n : ℕ) := by exact_mod_cast hn.trans (hφ.id_le n)
    linarith [hnorm (φ n)]
  have hb : ‖a * b (φ n)‖ ≤ 1 := calc
    ‖a * b (φ n)‖ = ‖b (φ n)‖ * ‖a‖ := by rw [norm_mul, mul_comm]
    _ ≤ ‖b (φ n)‖ * ‖x (φ n)‖ := mul_le_mul_of_nonneg_left ha (norm_nonneg _)
    _ ≤ 1 := by simpa [norm_smul] using (hbupper (φ n)).le
  simpa [y, mul_smul] using hstable (a * b (φ n)) hb (x (φ n)) (hx (φ n))

open RadicalConductor

/-- Clearing scalar denominators on the finitely many coordinate vectors makes the
subring open and closed in coordinates, using its stability under integral scalars. -/
theorem isClosed_subring_coordinates {K W ι : Type*} [NontriviallyNormedField K]
    [Fintype ι] [CommRing W] [Algebra K W] (e : (ι → K) ≃ₗ[K] W) (T : Subring W)
    (hstable : ∀ (b : K), ‖b‖ ≤ 1 → ∀ w ∈ T, b • w ∈ T)
    (hclear : ∀ w : W, ∃ c : K, c ≠ 0 ∧ c • w ∈ T) :
    IsClosed (e ⁻¹' (T : Set W)) := by
  classical
  let v := Pi.basisFun K ι
  choose c hc hmem using fun i ↦ hclear (e (v i))
  let S := T.toAddSubgroup.comap e.toAddMonoidHom
  apply S.isClosed_of_isOpen
  apply S.isOpen_of_mem_nhds (g := 0)
  have hsmall (i : ι) : ∀ᶠ x : ι → K in 𝓝 0, ‖x i‖ ≤ ‖c i‖ := by
    apply Filter.Tendsto.eventually_le_const (norm_pos_iff.mpr (hc i))
    simpa [Function.comp_def] using ((continuous_norm.comp (continuous_apply i)).tendsto (0 : ι → K))
  filter_upwards [Filter.eventually_all.mpr hsmall] with x hx
  change e x ∈ T
  rw [← v.sum_repr x, map_sum]
  apply T.sum_mem
  intro i _
  have hsmall' : ‖x i / c i‖ ≤ 1 := by
    rw [norm_div, div_le_one₀ (norm_pos_iff.mpr (hc i))]
    exact hx i
  simpa [v, smul_smul, hc] using hstable (x i / c i) hsmall' _ (hmem i)

/-- A closed subring with zero conductor is bounded if scalar denominators clear and
the unit ball acts on it. Coordinates supply the norm on the ambient vector space. -/
theorem bounded_of_closed_zero_conductor {K E W : Type*} [NontriviallyNormedField K]
    [NormedAddCommGroup E] [NormedSpace K E] [ProperSpace E] [CommRing W] [Algebra K W]
    (e : E ≃ₗ[K] W) (T : Subring W) (hclosed : IsClosed (e ⁻¹' (T : Set W)))
    (hstable : ∀ (b : K), ‖b‖ ≤ 1 → ∀ w ∈ T, b • w ∈ T)
    (hclear : ∀ w : W, ∃ c : K, c ≠ 0 ∧ c • w ∈ T) (hzero : conductorIdeal T = ⊥) :
    ∃ R : ℝ, ∀ x : E, e x ∈ T → ‖x‖ ≤ R := by
  by_contra! hunbounded
  obtain ⟨v, hv, hline⟩ := exists_line_of_unbounded (K := K) (e ⁻¹' (T : Set W)) hclosed
    (fun b hb x hx ↦ by
      change e (b • x) ∈ T
      rw [map_smul]
      exact hstable b hb (e x) hx) hunbounded
  have hmem : e v ∈ conductorIdeal T := by
    intro x
    obtain ⟨c, hc, hx⟩ := hclear x
    have hv' : c⁻¹ • e v ∈ T := by simpa using hline c⁻¹
    simpa [smul_mul_smul_comm, hc] using T.mul_mem hv' hx
  rw [hzero, Ideal.mem_bot] at hmem
  exact hv (e.map_eq_zero_iff.mp hmem)

/-- The actual scalar-extended image modulo its full conductor has zero conductor.
This lets boundedness apply directly to the finite-dimensional quotient. -/
theorem quotient_image_conductor_eq_bot {B : Type*} [CommRing B] (T : Subring B) :
    conductorIdeal (T.map (Ideal.Quotient.mk (conductorIdeal T))) = ⊥ :=
  quotient_image_ideal_eq_bot T _ (conductorIdeal_subset _)

/-- Every linear functional on the finite-dimensional conductor quotient is bounded
on the image of the original subring. -/
theorem bounded_linear_observation_mod_conductor {K B Y : Type*}
    [NontriviallyNormedField K] [CompleteSpace K] [ProperSpace K] [CommRing B] [Algebra K B]
    [NormedAddCommGroup Y] [NormedSpace K Y]
    (T : Subring B) (hstable : ∀ (b : K), ‖b‖ ≤ 1 → ∀ x ∈ T, b • x ∈ T)
    (hclear : ∀ x : B, ∃ c : K, c ≠ 0 ∧ c • x ∈ T)
    [FiniteDimensional K (B ⧸ conductorIdeal T)] (L : (B ⧸ conductorIdeal T) →ₗ[K] Y) :
    ∃ R : ℝ, ∀ x ∈ T, ‖L (Ideal.Quotient.mk _ x)‖ ≤ R := by
  let W := B ⧸ conductorIdeal T
  let N := Module.finrank K W
  let e : (Fin N → K) ≃ₗ[K] W := (Module.finBasis K W).equivFun.symm
  let q := Ideal.Quotient.mkₐ K (conductorIdeal T)
  let C := T.map q.toRingHom
  have hC (b : K) (hb : ‖b‖ ≤ 1) (w : W) (hw : w ∈ C) : b • w ∈ C := by
    obtain ⟨x, hx, rfl⟩ := hw
    exact ⟨b • x, hstable b hb x hx, map_smul q b x⟩
  have hCW (w : W) : ∃ c : K, c ≠ 0 ∧ c • w ∈ C := by
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective w
    obtain ⟨c, hc, hx⟩ := hclear x
    exact ⟨c, hc, c • x, hx, map_smul q c x⟩
  obtain ⟨r, hr⟩ := bounded_of_closed_zero_conductor e C
    (isClosed_subring_coordinates e C hC hCW) hC hCW (quotient_image_conductor_eq_bot T)
  let l := (L.comp e.toLinearMap).toContinuousLinearMap
  refine ⟨‖l‖ * r, fun x hx ↦ ?_⟩
  let v := e.symm (q x)
  have hv : e v ∈ C := by simpa [v] using (show q x ∈ C from ⟨x, hx, rfl⟩)
  have hl := (l.le_opNorm v).trans (mul_le_mul_of_nonneg_left (hr v hv) (norm_nonneg l))
  simpa [l, v, q] using hl

end UnconditionalCounterexample.Variations
