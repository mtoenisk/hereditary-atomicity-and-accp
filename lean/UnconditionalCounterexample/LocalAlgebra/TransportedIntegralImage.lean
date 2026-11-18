import UnconditionalCounterexample.LocalAlgebra.IntegralTensorImage

/-!
# Integral tensor images under an actual algebra equivalence

Transport the ordinary algebraic integral tensor image through a specified
Qp-algebra equivalence. Integral scalars and original elements belong to this
image. Rational integer clearing gives elementwise p-power clearing, and
finite tensor-sum induction extends integral evaluation bounds from the
original subring. No topological closure or module-finiteness is used.
-/

noncomputable section
namespace UnconditionalCounterexample.LocalAlgebra.TransportedIntegralImage

open scoped TensorProduct

variable (p : ℕ) [Fact p.Prime]
    (B A : Type*) [CommRing B] [Algebra ℚ B] [CommRing A] [Algebra ℚ_[p] A]
    (e : ℚ_[p] ⊗[ℚ] B ≃ₐ[ℚ_[p]] A)

def image (T : Subring B) : Subring A :=
  (IntegralTensorImage.image p B T).map e.toRingHom

theorem original_mem (T : Subring B) (t : T) :
    e ((1 : ℚ_[p]) ⊗ₜ[ℚ] (t : B)) ∈ image p B A e T :=
  ⟨_, IntegralTensorImage.tmul_mem_image p B T t 1, rfl⟩

theorem scalar_mem (T : Subring B) (c : ℚ_[p]) (hc : c ∈ PadicInt.subring p) :
    algebraMap ℚ_[p] A c ∈ image p B A e T := by
  refine ⟨c ⊗ₜ[ℚ] (1 : B), ?_, ?_⟩
  · exact IntegralTensorImage.tmul_mem_image p B T 1 ⟨c, hc⟩
  · exact e.commutes c

theorem exists_power_mul_mem (T : Subring B)
    (hclear : ∀ b : B, ∃ n : ℕ, 0 < n ∧ (n : B) * b ∈ T)
    (z : A) : ∃ k : ℕ, (p : A) ^ k * z ∈ image p B A e T := by
  obtain ⟨k, hk⟩ := IntegralTensorImage.exists_power_mul_mem_image p B T hclear (e.symm z)
  refine ⟨k, _, hk, ?_⟩
  change e ((p : ℚ_[p] ⊗[ℚ] B) ^ k * e.symm z) = (p : A) ^ k * z
  simp only [map_mul, map_pow, map_natCast, AlgEquiv.apply_symm_apply]

theorem exists_scalar_mul_mem (T : Subring B)
    (hclear : ∀ b : B, ∃ n : ℕ, 0 < n ∧ (n : B) * b ∈ T)
    (z : A) : ∃ c : ℚ_[p], c ≠ 0 ∧ algebraMap ℚ_[p] A c * z ∈ image p B A e T := by
  obtain ⟨k, hk⟩ := exists_power_mul_mem p B A e T hclear z
  refine ⟨(p : ℚ_[p]) ^ k, pow_ne_zero k ?_, ?_⟩
  · exact_mod_cast (Fact.out : p.Prime).ne_zero
  · simpa only [map_pow, map_natCast] using hk

theorem eval_tmul (v : A →ₐ[ℚ_[p]] ℚ_[p]) (c : ℚ_[p]) (b : B) :
    v (e (c ⊗ₜ[ℚ] b)) = c * v (e ((1 : ℚ_[p]) ⊗ₜ[ℚ] b)) := by
  have heq : c ⊗ₜ[ℚ] b =
      algebraMap ℚ_[p] (ℚ_[p] ⊗[ℚ] B) c * ((1 : ℚ_[p]) ⊗ₜ[ℚ] b) := by
    change c ⊗ₜ[ℚ] b = (c ⊗ₜ[ℚ] (1 : B)) * ((1 : ℚ_[p]) ⊗ₜ[ℚ] b)
    simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  rw [heq, map_mul, e.commutes, map_mul, v.commutes]
  rfl

theorem integral_values (T : Subring B) (v : A →ₐ[ℚ_[p]] ℚ_[p])
    (hv : ∀ t : T, v (e ((1 : ℚ_[p]) ⊗ₜ[ℚ] (t : B))) ∈ PadicInt.subring p)
    (z : A) (hz : z ∈ image p B A e T) : v z ∈ PadicInt.subring p := by
  obtain ⟨x, hx, rfl⟩ := hz
  obtain ⟨y, rfl⟩ := hx
  induction y using TensorProduct.inductionOn with
  | tmul t c =>
    rw [IntegralTensorImage.tensorMap_tmul]
    change v (e ((c : ℚ_[p]) ⊗ₜ[ℚ] (t : B))) ∈ PadicInt.subring p
    rw [eval_tmul]
    exact (PadicInt.subring p).mul_mem c.property (hv t)
  | add x y hx hy =>
    simp only [map_add]
    exact (PadicInt.subring p).add_mem hx hy

theorem norm_values_le_one (T : Subring B) (v : A →ₐ[ℚ_[p]] ℚ_[p])
    (hv : ∀ t : T, ‖v (e ((1 : ℚ_[p]) ⊗ₜ[ℚ] (t : B)))‖ ≤ 1)
    (z : A) (hz : z ∈ image p B A e T) : ‖v z‖ ≤ 1 := by
  apply (PadicInt.mem_subring_iff _).mp
  exact integral_values p B A e T v (fun t => (PadicInt.mem_subring_iff _).mpr (hv t)) z hz

end UnconditionalCounterexample.LocalAlgebra.TransportedIntegralImage
