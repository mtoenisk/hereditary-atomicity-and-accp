import UnconditionalCounterexample.Variations.DimensionConductorEquality
import UnconditionalCounterexample.LocalAlgebra.TransportedIntegralImage
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.Analysis.Normed.Group.Ultra

/-!
# The actual p-adic tensor image in the multivariate conductor theorem

The integer tensor image embeds in the rational scalar extension. Clearing
integer denominators and testing integral values at the original elements
supply the scalar and evaluation hypotheses for the local conductor proof.
Finite residue extensions are allowed at every closed point.
-/

namespace UnconditionalCounterexample.Variations

open LocalAlgebra LocalAlgebra.TransportedIntegralImage RadicalConductor
open scoped TensorProduct

variable (p : ℕ) [Fact p.Prime] (B A : Type*) [CommRing B] [Algebra ℚ B] [CommRing A]
  [Algebra ℚ_[p] A] (e : ℚ_[p] ⊗[ℚ] B ≃ₐ[ℚ_[p]] A) (T : Subring B)

/-- All elements of the honest integral tensor image have integral values in a normed
residue extension when this holds for the elements of the original subring. -/
theorem norm_value_le_one_tensorImage {E : Type*} [NontriviallyNormedField E] [IsUltrametricDist E]
    [NormedAlgebra ℚ_[p] E] (v : A →ₐ[ℚ_[p]] E)
    (hv : ∀ t : T, ‖v (e ((1 : ℚ_[p]) ⊗ₜ[ℚ] (t : B)))‖ ≤ 1)
    (z : A) (hz : z ∈ image p B A e T) : ‖v z‖ ≤ 1 := by
  obtain ⟨x, hx, rfl⟩ := hz
  obtain ⟨y, rfl⟩ := hx
  induction y using TensorProduct.inductionOn with
  | tmul t c =>
    rw [IntegralTensorImage.tensorMap_tmul]
    change ‖v (e ((c : ℚ_[p]) ⊗ₜ[ℚ] (t : B)))‖ ≤ 1
    have h : (c : ℚ_[p]) ⊗ₜ[ℚ] (t : B) =
        algebraMap ℚ_[p] (ℚ_[p] ⊗[ℚ] B) (c : ℚ_[p]) * ((1 : ℚ_[p]) ⊗ₜ[ℚ] (t : B)) := by
      change _ = ((c : ℚ_[p]) ⊗ₜ[ℚ] (1 : B)) * ((1 : ℚ_[p]) ⊗ₜ[ℚ] (t : B))
      simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [h, map_mul, e.commutes, map_mul, v.commutes, norm_mul, norm_algebraMap']
    simpa using mul_le_mul (show ‖(c : ℚ_[p])‖ ≤ 1 from c.property) (hv t) (norm_nonneg _) zero_le_one
  | add x y hx hy =>
    simp only [map_add]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hx hy)

/-- The uniformizer viewed as an ambient unit in the rational scalar extension. -/
noncomputable def localPrimeUnit : Aˣ :=
  Units.map (algebraMap ℚ_[p] A).toMonoidHom
    (Units.mk0 (p : ℚ_[p]) (by exact_mod_cast (Fact.out : p.Prime).ne_zero))

/-- The local conductor equality in the transported image of the actual algebraic
tensor product, from the coefficient transfers and directional escape in this ring. -/
theorem tensorImage_conductor_eq {ι : Type*} [Finite ι] {E : ι → Type*}
    [∀ i, NontriviallyNormedField (E i)] [∀ i, IsUltrametricDist (E i)]
    [∀ i, NormedAlgebra ℚ_[p] (E i)] [∀ i, FiniteDimensional ℚ_[p] (E i)] [IsNoetherianRing A]
    (ev : ∀ i, A →ₐ[ℚ_[p]] E i) (hsurj : Function.Surjective (AlgHom.pi ev))
    (hval : ∀ i (t : T), ‖ev i (e ((1 : ℚ_[p]) ⊗ₜ[ℚ] (t : B)))‖ ≤ 1)
    (hclear : ∀ b : B, ∃ n : ℕ, 0 < n ∧ (n : B) * b ∈ T)
    (F : Polynomial (image p B A e T)) (a : ℕ)
    (hgen : (F.map (image p B A e T).subtype).contentIdeal = ⨅ i, RingHom.ker (ev i))
    (hword : ∀ n : ℕ, ∃ i ≥ n, ∃ P δ : image p B A e T,
        (P : A) - (F.map (image p B A e T).subtype).eval ((p : A)^i) = (p : A)^(i*i) * δ ∧
        (↑((localPrimeUnit p A)⁻¹) : A)^(i*i) * (P : A)^a ∈ image p B A e T)
    (hesc : ∀ i, ∀ δ : A →ₗ[ℚ_[p]] E i, δ ≠ 0 →
      (∀ x y, δ (x*y) = ev i x * δ y + ev i y * δ x) →
      ∀ R : ℝ, ∃ x ∈ image p B A e T, R < ‖δ x‖) :
    conductorIdeal (image p B A e T) = ⨅ i, RingHom.ker (ev i) := by
  classical
  let U := image p B A e T
  let u := localPrimeUnit p A
  have hu : (u : A) = (p : A) := by simp [u, localPrimeUnit]
  have huT : (u : A) ∈ U := by rw [hu]; exact natCast_mem U p
  have he (i : ι) : Function.Surjective (ev i) := by
    intro x
    obtain ⟨v, hv⟩ := hsurj (Pi.single i x)
    exact ⟨v, by simpa using congrFun hv i⟩
  have hr := radical_conductor_of_approximating_words U u huT (fun x ↦ hu ▸
    exists_power_mul_mem p B A e T hclear x) F a (fun i ↦ (ev i).toRingHom) he
    (fun i ↦ norm_value_le_one_tensorImage p B A e T (ev i) (hval i)) hgen (by simpa only [hu] using hword)
  apply conductor_eq_point_kernels_of_directional_escape U ev hsurj hr ?_ ?_ hesc
  · intro c hc z hz
    rw [Algebra.smul_def]
    exact U.mul_mem (scalar_mem p B A e T c ((PadicInt.mem_subring_iff p).mpr hc)) hz
  · intro x
    simpa only [Algebra.smul_def] using exists_scalar_mul_mem p B A e T hclear x

end UnconditionalCounterexample.Variations
