import UnconditionalCounterexample.GuardSupport
import UnconditionalCounterexample.Variations.GuardInterpolation
import UnconditionalCounterexample.LocalAlgebra.TransportedIntegralImage

/-!
# Integral evaluation in the tensor image at a good prime

If one integer multiple of a coordinate belongs to the original subring,
then the coordinate itself lies in the integral tensor image away from the
prime divisors of that integer. Surjective integral polynomial evaluation
at that coordinate and containment of the evaluation kernel transfer all
integral values to the tensor image.
-/

noncomputable section

namespace UnconditionalCounterexample.Variations.GuardUnramified

open Polynomial LocalAlgebra.TransportedIntegralImage
open scoped TensorProduct

/-- Interpolation with integral scalar coefficients and the kernel inclusion
recover every element whose vector of values belongs to the integral product. -/
theorem mem_of_integral_values {R A O E : Type*} [CommRing R] [CommRing A] [CommRing O] [CommRing E]
    (U : Subring A) (c : R →+* U) (o : R →+* O) (j : O →+* E) (g : A →+* E)
    (hscalar : (g.comp U.subtype).comp c = j.comp o) (t : U) (x : O) (ht : g t = j x)
    (hs : Function.Surjective (eval₂RingHom o x))
    (hk : ∀ z ∈ RingHom.ker g, z ∈ U) (z : A) (hz : g z ∈ Set.range j) : z ∈ U := by
  obtain ⟨v, hv⟩ := hz
  obtain ⟨P, hP⟩ := hs v
  let h := eval₂RingHom c t
  have e : (g.comp U.subtype).comp h = j.comp (eval₂RingHom o x) := by
    apply Polynomial.ringHom_ext
    · intro a
      simpa [h] using DFunLike.congr_fun hscalar a
    · simpa [h] using ht
  have hval : g (h P) = g z := (DFunLike.congr_fun e P).trans ((congrArg j hP).trans hv)
  have hd := hk (z - h P) (by change g (z - h P) = 0; rw [map_sub, hval, sub_self])
  simpa using U.add_mem hd (h P).property

variable (p : ℕ) [Fact p.Prime] (B A : Type*) [CommRing B] [Algebra ℚ B]
  [CommRing A] [Algebra ℚ_[p] A] (e : ℚ_[p] ⊗[ℚ] B ≃ₐ[ℚ_[p]] A) (T : Subring B)

/-- The integral scalar map into the actual transported tensor image. -/
def tensorScalars : ℤ_[p] →+* image p B A e T :=
  ((algebraMap ℚ_[p] A).comp (algebraMap ℤ_[p] ℚ_[p])).codRestrict _
    (fun a => scalar_mem p B A e T (a : ℚ_[p]) a.property)

theorem coordinate_mem_of_prime_to (b : B) (n : ℕ) (hnt : (n : B) * b ∈ T) (hp : ¬ p ∣ n) :
    e ((1 : ℚ_[p]) ⊗ₜ[ℚ] b) ∈ image p B A e T := by
  let U := image p B A e T
  let f := e.toRingHom.comp (Algebra.TensorProduct.includeRight (R := ℚ) (A := ℚ_[p]) (B := B)).toRingHom
  have hnt' : (n : A) * f b ∈ U := by
    have h := original_mem p B A e T ⟨_, hnt⟩
    change f ((n : B) * b) ∈ U at h
    simpa only [map_mul, map_natCast] using h
  have hu : IsUnit (n : ℤ_[p]) := (GuardSupport.padicInt_isUnit_iff_toZMod_ne_zero _).mpr (by
    rw [map_natCast]
    exact fun h => hp ((ZMod.natCast_eq_zero_iff n p).mp h))
  obtain ⟨a, ha⟩ := hu
  let c := tensorScalars p B A e T
  have hmul : (c a⁻¹.val : A) * (n : A) = 1 := by
    change ((U.subtype.comp c) _) * (n : A) = 1
    rw [← map_natCast (U.subtype.comp c) n, ← ha, ← map_mul]
    simp
  have h := U.mul_mem (c a⁻¹.val).property hnt'
  rwa [← mul_assoc, hmul, one_mul] at h

end UnconditionalCounterexample.Variations.GuardUnramified
