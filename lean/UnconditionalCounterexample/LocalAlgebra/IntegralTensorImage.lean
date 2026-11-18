import UnconditionalCounterexample.LocalAlgebra.PadicMembership
import Mathlib.RingTheory.Localization.BaseChange

/-!
# Actual integral p-adic tensor images

For a commutative rational algebra `B` and any unital subring `T`, this module
constructs the injective map from `T ⊗[ℤ] ℤ_[p]` to `ℚ_[p] ⊗[ℚ] B`, and its
left-oriented version. Their common image is the ordinary algebraic tensor
image, with an explicit bridge to the integer-lattice descent theorem.

If every element of `B` can be multiplied into `T` by a positive integer,
then `ℚ_[p] ⊗[ℚ] B` is the localization of this image at the powers of `p`.
No field identification or topological closure is used.

Coefficient localization and comparison of tensor images work in an arbitrary
commutative rational algebra.
-/

namespace UnconditionalCounterexample.LocalAlgebra.IntegralTensorImage

open scoped TensorProduct nonZeroDivisors

noncomputable section

/-- Ordinary nonzero integer denominators already generate the entire p-adic
field from the p-adic integers. -/
theorem padic_isLocalization_integer_denominators (p : ℕ) [Fact p.Prime] :
    IsLocalization (Algebra.algebraMapSubmonoid (PadicInt p) (nonZeroDivisors ℤ))
      (Padic p) := by
  let M := Algebra.algebraMapSubmonoid (PadicInt p) (nonZeroDivisors ℤ)
  have hle : M ≤ nonZeroDivisors (PadicInt p) := by
    rintro x ⟨z, hz, rfl⟩
    apply mem_nonZeroDivisors_iff_ne_zero.mpr
    change (z : PadicInt p) ≠ 0
    exact Int.cast_ne_zero.mpr (mem_nonZeroDivisors_iff_ne_zero.mp hz)
  have hcofinal : ∀ x ∈ nonZeroDivisors (PadicInt p), ∃ y ∈ M, x ∣ y := by
    intro x hx
    obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
      (mem_nonZeroDivisors_iff_ne_zero.mp hx) (PadicInt.irreducible_p (p := p))
    refine ⟨(p : PadicInt p) ^ n, ?_, ?_⟩
    · refine ⟨(p : ℤ) ^ n, ?_, ?_⟩
      · apply mem_nonZeroDivisors_iff_ne_zero.mpr
        exact pow_ne_zero n (by exact_mod_cast (Fact.out : p.Prime).ne_zero)
      · simp
    · refine ⟨(↑u⁻¹ : PadicInt p), ?_⟩
      simp [mul_comm, mul_left_comm]
  exact (IsLocalization.iff_of_le_of_exists_dvd M (nonZeroDivisors (PadicInt p))
    hle hcofinal).mpr inferInstance

/-- The exact rational scalar extension of the actual p-adic integer ring. -/
def rationalPadicIntEquiv (p : ℕ) [Fact p.Prime] :
    (ℚ ⊗[ℤ] PadicInt p) ≃ₐ[ℚ] Padic p := by
  letI := padic_isLocalization_integer_denominators p
  have h := (Algebra.isLocalization_iff_isPushout (nonZeroDivisors ℤ) ℚ
    (T := PadicInt p) (B := Padic p)).mp inferInstance
  letI := h.symm
  exact Algebra.IsPushout.equiv ℤ ℚ (PadicInt p) (Padic p)

@[simp]
theorem rationalPadicIntEquiv_tmul (p : ℕ) [Fact p.Prime] (q : ℚ) (z : PadicInt p) :
    rationalPadicIntEquiv p (q ⊗ₜ[ℤ] z) = algebraMap ℚ (Padic p) q * z := by
  simp only [rationalPadicIntEquiv, Algebra.IsPushout.equiv_tmul, PadicInt.algebraMap_apply]

/-- A rational algebra's p-adic integer tensor is canonically its rational
p-adic tensor. -/
def algebraPadicTensorEquiv (p : ℕ) [Fact p.Prime]
    (F : Type*) [CommRing F] [Algebra ℚ F] :
    (F ⊗[ℤ] PadicInt p) ≃ₐ[F] (F ⊗[ℚ] Padic p) :=
  (Algebra.TensorProduct.cancelBaseChange ℤ ℚ F F (PadicInt p)).symm.trans
    (Algebra.TensorProduct.congr (AlgEquiv.refl : F ≃ₐ[F] F) (rationalPadicIntEquiv p))

@[simp]
theorem algebraPadicTensorEquiv_tmul (p : ℕ) [Fact p.Prime]
    (F : Type*) [CommRing F] [Algebra ℚ F] (x : F) (z : PadicInt p) :
    algebraPadicTensorEquiv p F (x ⊗ₜ[ℤ] z) = x ⊗ₜ[ℚ] (z : Padic p) := by
  simp [algebraPadicTensorEquiv, Algebra.TensorProduct.congr]

variable (p : ℕ) [Fact p.Prime] (B : Type*) [CommRing B] [Algebra ℚ B]

/-- Explicit comparison with the left-oriented rational scalar extension. -/
def ambientEquiv : (B ⊗[ℤ] PadicInt p) ≃+* (Padic p ⊗[ℚ] B) :=
  (algebraPadicTensorEquiv p B).toRingEquiv.trans
    (Algebra.TensorProduct.comm ℚ B (Padic p)).toRingEquiv

@[simp] theorem ambientEquiv_tmul (b : B) (z : PadicInt p) :
    ambientEquiv p B (b ⊗ₜ[ℤ] z) = (z : Padic p) ⊗ₜ[ℚ] b := by
  simp [ambientEquiv]

/-- Actual inclusion of the integral tensor of a subring. -/
def tensorInclusion (T : Subring B) :
    T ⊗[ℤ] PadicInt p →ₐ[ℤ] B ⊗[ℤ] PadicInt p :=
  Algebra.TensorProduct.map T.subtype.toIntAlgHom (AlgHom.id ℤ (PadicInt p))

def tensorMap (T : Subring B) :
    T ⊗[ℤ] PadicInt p →+* Padic p ⊗[ℚ] B :=
  (ambientEquiv p B).toRingHom.comp (tensorInclusion p B T).toRingHom

@[simp] theorem tensorMap_tmul (T : Subring B) (t : T) (z : PadicInt p) :
    tensorMap p B T (t ⊗ₜ[ℤ] z) = (z : Padic p) ⊗ₜ[ℚ] (t : B) := by
  exact ambientEquiv_tmul p B t z

theorem tensorMap_injective (T : Subring B) : Function.Injective (tensorMap p B T) := by
  apply (ambientEquiv p B).injective.comp
  exact Module.Flat.rTensor_preserves_injective_linearMap
    T.subtype.toIntAlgHom.toLinearMap Subtype.val_injective

/-- Ordinary algebraic tensor image; this is not a topological closure. -/
def image (T : Subring B) : Subring (Padic p ⊗[ℚ] B) := (tensorMap p B T).range

theorem tmul_mem_image (T : Subring B) (t : T) (z : PadicInt p) :
    (z : Padic p) ⊗ₜ[ℚ] (t : B) ∈ image p B T :=
  ⟨t ⊗ₜ[ℤ] z, tensorMap_tmul p B T t z⟩

theorem ambientEquiv_mem_image_iff (T : Subring B) (x : B ⊗[ℤ] PadicInt p) :
    ambientEquiv p B x ∈ image p B T ↔
      x ∈ LocalOrderTensor.tensorImage (PadicInt p) T.toAddSubgroup.toIntSubmodule := by
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨y, (ambientEquiv p B).injective hy⟩
  · rintro ⟨y, hy⟩
    exact ⟨y, congrArg (ambientEquiv p B) hy⟩

/-- Every p-adic coefficient becomes integral after multiplication by a power
of the ordinary rational prime. -/
theorem exists_power_mul_integral (x : Padic p) :
    ∃ n : ℕ, ∃ z : PadicInt p, (z : Padic p) = (p : Padic p) ^ n * x := by
  by_cases hx : x = 0
  · exact ⟨0, 0, by simp [hx]⟩
  let n := (-x.valuation).toNat
  have hp : (p : Padic p) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hv : 0 ≤ ((p : Padic p) ^ n * x).valuation := by
    rw [Padic.valuation_mul (pow_ne_zero _ hp) hx, Padic.valuation_pow,
      Padic.valuation_p, mul_one]
    have h := Int.self_le_toNat (-x.valuation)
    dsimp [n]
    omega
  exact ⟨n, ⟨_, (Padic.norm_le_one_iff_val_nonneg _).mpr hv⟩, rfl⟩

/-- Integer clearing in the original algebra supplies power clearing in the
actual rational p-adic tensor. No module-finiteness hypothesis is needed. -/
theorem exists_power_mul_mem_image (T : Subring B)
    (hclear : ∀ b : B, ∃ n : ℕ, 0 < n ∧ (n : B) * b ∈ T)
    (x : Padic p ⊗[ℚ] B) :
    ∃ k : ℕ, (p : Padic p ⊗[ℚ] B) ^ k * x ∈ image p B T := by
  induction x using TensorProduct.inductionOn with
  | tmul c b =>
    obtain ⟨n, hn, hnb⟩ := hclear b
    obtain ⟨k, z, hz⟩ := exists_power_mul_integral p (c / (n : Padic p))
    refine ⟨k, ?_⟩
    have hn' : (n : Padic p) ≠ 0 := by exact_mod_cast hn.ne'
    have heq : (z : Padic p) ⊗ₜ[ℚ] ((n : B) * b) =
        ((p : Padic p) ^ k * c) ⊗ₜ[ℚ] b := by
      have hsmul : (n : B) * b = (n : ℚ) • b := by simp [Algebra.smul_def]
      rw [hsmul, TensorProduct.tmul_smul]
      apply congrArg (fun d : Padic p => d ⊗ₜ[ℚ] b)
      simp only [Algebra.smul_def, map_natCast, hz]
      field_simp
    have hm := tmul_mem_image p B T ⟨(n : B) * b, hnb⟩ z
    rw [heq] at hm
    convert hm using 1
    rw [← map_natCast (algebraMap (Padic p) (Padic p ⊗[ℚ] B)), ← map_pow]
    change (((p : Padic p) ^ k) ⊗ₜ[ℚ] (1 : B)) * (c ⊗ₜ[ℚ] b) = _
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  | add x y hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    refine ⟨a + b, ?_⟩
    have hpa := (image p B T).pow_mem (natCast_mem (image p B T) p) a
    have hpb := (image p B T).pow_mem (natCast_mem (image p B T) p) b
    have h := (image p B T).add_mem ((image p B T).mul_mem hpb ha)
      ((image p B T).mul_mem hpa hb)
    convert h using 1
    ring

/-- The same actual inclusion with p-adic integers in the left tensor factor. -/
def leftTensorMap (T : Subring B) :
    PadicInt p ⊗[ℤ] T →+* Padic p ⊗[ℚ] B :=
  (tensorMap p B T).comp (Algebra.TensorProduct.comm ℤ (PadicInt p) T).toRingHom

@[simp] theorem leftTensorMap_tmul (T : Subring B) (z : PadicInt p) (t : T) :
    leftTensorMap p B T (z ⊗ₜ[ℤ] t) = (z : Padic p) ⊗ₜ[ℚ] (t : B) := by
  simp [leftTensorMap]

theorem leftTensorMap_injective (T : Subring B) :
    Function.Injective (leftTensorMap p B T) :=
  (tensorMap_injective p B T).comp (Algebra.TensorProduct.comm ℤ (PadicInt p) T).injective

theorem leftTensorMap_range (T : Subring B) : (leftTensorMap p B T).range = image p B T := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨Algebra.TensorProduct.comm ℤ (PadicInt p) T y, rfl⟩
  · rintro ⟨y, rfl⟩
    exact ⟨(Algebra.TensorProduct.comm ℤ (PadicInt p) T).symm y, by simp [leftTensorMap]⟩

/-- The rational scalar extension is literally the localization of the actual
integral tensor image at the powers of p. -/
theorem isLocalization_image (T : Subring B)
    (hclear : ∀ b : B, ∃ n : ℕ, 0 < n ∧ (n : B) * b ∈ T) :
    IsLocalization (Submonoid.powers (p : image p B T)) (Padic p ⊗[ℚ] B) := by
  rw [isLocalization_iff]
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨y, n, rfl⟩
    simp only [map_pow, map_natCast]
    have hp : (p : Padic p) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
    have hu := (isUnit_iff_ne_zero.mpr hp).map (algebraMap (Padic p) (Padic p ⊗[ℚ] B))
    simpa only [map_natCast] using hu.pow n
  · intro x
    obtain ⟨n, hn⟩ := exists_power_mul_mem_image p B T hclear x
    refine ⟨(⟨(p : Padic p ⊗[ℚ] B) ^ n * x, hn⟩, ⟨(p : image p B T) ^ n, n, rfl⟩), ?_⟩
    change x * (p : Padic p ⊗[ℚ] B) ^ n = (p : Padic p ⊗[ℚ] B) ^ n * x
    exact mul_comm _ _
  · intro x y hxy
    exact ⟨1, by simpa using Subtype.ext hxy⟩

/-- Exact descent from the actual integral tensor images, for arbitrary unital
subrings and with no finite-generation assumption. -/
theorem mem_iff_mem_all_images (T : Subring B) (b : B) :
    b ∈ T ↔ ∀ (p : ℕ) (_ : Fact p.Prime),
      (1 : Padic p) ⊗ₜ[ℚ] b ∈ image p B T := by
  change b ∈ T.toAddSubgroup.toIntSubmodule ↔ _
  rw [integerLattice_mem_iff_mem_all_padicImages T.toAddSubgroup.toIntSubmodule b]
  apply forall_congr'
  intro p
  apply forall_congr'
  intro hp
  rw [← ambientEquiv_mem_image_iff p B T]
  simp

/-- Inclusion of original subrings gives inclusion of their actual integral
tensor images. -/
theorem image_mono {T D : Subring B} (hTD : T ≤ D) : image p B T ≤ image p B D := by
  rintro x ⟨y, rfl⟩
  induction y using TensorProduct.inductionOn with
  | tmul t z =>
    rw [tensorMap_tmul]
    exact tmul_mem_image p B D ⟨t, hTD t.property⟩ z
  | add x y hx hy =>
    rw [map_add]
    exact (image p B D).add_mem hx hy

/-- A single integer conductor in every actual p-adic image descends to the
original subrings, without finite generation over the integers. -/
theorem integer_conductor_of_all_images (T D : Subring B) (n : ℤ)
    (hlocal : ∀ (p : ℕ) (_ : Fact p.Prime), ∀ x ∈ image p B D,
      (n : Padic p ⊗[ℚ] B) * x ∈ image p B T) :
    ∀ d ∈ D, (n : B) * d ∈ T := by
  intro d hd
  apply (mem_iff_mem_all_images B T ((n : B) * d)).mpr
  intro p hp
  have h := hlocal p hp ((1 : Padic p) ⊗ₜ[ℚ] d)
    (tmul_mem_image p B D ⟨d, hd⟩ 1)
  have heq : (1 : Padic p) ⊗ₜ[ℚ] ((n : B) * d) =
      (n : Padic p ⊗[ℚ] B) * ((1 : Padic p) ⊗ₜ[ℚ] d) := by
    change Algebra.TensorProduct.includeRight ((n : B) * d) = _
    rw [map_mul, map_intCast]
    rfl
  rwa [← heq] at h

end
end UnconditionalCounterexample.LocalAlgebra.IntegralTensorImage
