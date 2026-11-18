import UnconditionalCounterexample.PoleTensorConductor

/-!
# The exact scale from a prescribed integer clearing t

For the same positive integer n with nt in the original subring, the scalar
p^(nu_p(n))/n has valuation zero and is integral. Multiplication of its actual
scalar image by the original nt pure tensor yields p^(nu_p(n))*t in the actual
transported integral image. This verifies the precise scale chosen at the
start of manuscript Lemma 6.1, without choosing a different integer or a
larger exponent. The existing arbitrary-scale conductor proof remains valid.
-/

noncomputable section
namespace UnconditionalCounterexample.PaperConductorScale

open Polynomial TensorProduct LocalAlgebra PoleTensorConductor

variable (p : ℕ) [Fact p.Prime]

/-- The prescribed integer's p-part divided by that integer is an integral
p-adic scalar. Its valuation is exactly zero. -/
theorem normalizingScalar_valuation (n : ℕ) (hn : n ≠ 0) :
    ((p : ℚ_[p]) ^ padicValNat p n / (n : ℚ_[p])).valuation = 0 := by
  have hp : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  have hn' : (n : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr hn
  rw [div_eq_mul_inv, Padic.valuation_mul (pow_ne_zero _ hp) (inv_ne_zero hn'),
    Padic.valuation_pow, Padic.valuation_inv, Padic.valuation_p, Padic.valuation_natCast]
  simp

theorem normalizingScalar_integral (n : ℕ) (hn : n ≠ 0) :
    (p : ℚ_[p]) ^ padicValNat p n / (n : ℚ_[p]) ∈ PadicInt.subring p := by
  apply (Padic.norm_le_one_iff_val_nonneg _).mpr
  rw [normalizingScalar_valuation p n hn]

variable (S : Set ℚ[X]) (hS : ∀ f ∈ S, f ≠ 0)

/-- Original nt membership gives membership of the same n times the variable
in the actual transported integral tensor image. -/
theorem original_nat_mul_X_mem (T : Subring (PoleAlgebra.generated S)) (n : ℕ)
    (hnt : (n : PoleAlgebra.generated S) * algebraMap ℚ[X] (PoleAlgebra.generated S) X ∈ T) :
    (n : RatFunc ℚ_[p]) * RatFunc.X ∈ ambientImage p S hS T := by
  let B := PoleAlgebra.generated S
  let e := ScalarExtension.tensorEquiv ℚ ℚ_[p] S hS
  have h := (coe_mem_ambientImage_iff p S hS T _).mpr
    (TransportedIntegralImage.original_mem p B _ e T ⟨_, hnt⟩)
  have heq : (1 : ℚ_[p]) ⊗ₜ[ℚ] ((n : B) * algebraMap ℚ[X] B X) =
      (n : ℚ_[p] ⊗[ℚ] B) * ((1 : ℚ_[p]) ⊗ₜ[ℚ] algebraMap ℚ[X] B X) := by
    change Algebra.TensorProduct.includeRight ((n : B) * _) = _
    rw [map_mul, map_natCast]
    rfl
  change ScalarExtension.embedding ℚ ℚ_[p] S hS
    ((1 : ℚ_[p]) ⊗ₜ[ℚ] ((n : B) * algebraMap ℚ[X] B X)) ∈ ambientImage p S hS T at h
  rw [heq, map_mul, map_natCast] at h
  simpa only [B, ScalarExtension.embedding_tmul_polynomial, one_smul, Polynomial.map_X,
    RatFunc.algebraMap_X] using h

/-- The exact manuscript scale s=nu_p(n) works for every prescribed positive
integer n satisfying nt∈T. No replacement integer or enlarged p-power is chosen. -/
theorem prescribed_scale_mem (T : Subring (PoleAlgebra.generated S)) (n : ℕ) (hn : 0 < n)
    (hnt : (n : PoleAlgebra.generated S) * algebraMap ℚ[X] (PoleAlgebra.generated S) X ∈ T) :
    RatFunc.C (p : ℚ_[p]) ^ padicValNat p n * RatFunc.X ∈ ambientImage p S hS T := by
  have h := (ambientImage p S hS T).mul_mem
    (scalar_mem_ambientImage p S hS T _ (normalizingScalar_integral p n hn.ne'))
    (original_nat_mul_X_mem p S hS T n hnt)
  have hn' : (n : RatFunc ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  convert h using 1
  simp only [map_div₀, map_pow, map_natCast]
  field_simp

end UnconditionalCounterexample.PaperConductorScale
