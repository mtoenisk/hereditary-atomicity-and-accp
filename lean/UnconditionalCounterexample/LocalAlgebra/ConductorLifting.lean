import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.Algebra.Field.Basic

/-!
# Exact conductor lifting

A conductor between image subrings lifts when the kernel lies in the smaller subring.
The lifting uses algebraic membership and applies even when the smaller subring is not
an ideal.

The localization lemma applies inside any ambient field. In the intended
application, `B' = ℚ_p ⊗[ℚ] B` is the localization of `ℚ_p[t]` at the selected
rational polynomials, embedded in `ℚ_p(t)`; it is not identified with that
entire field. The actual denominator-clearing property remains explicit.
-/

namespace UnconditionalCounterexample.LocalAlgebra

variable {R A : Type*} [CommRing R] [CommRing A]

/-- Exact image membership lifts when the actual kernel is already contained
in the subring. Surjectivity of the ring homomorphism is not required. -/
theorem mem_iff_map_mem_of_kernel_subset (T : Subring R) (f : R →+* A)
    (hker : ∀ x : R, f x = 0 → x ∈ T) (x : R) :
    x ∈ T ↔ f x ∈ T.map f := by
  constructor
  · intro hx
    exact ⟨x, hx, rfl⟩
  · rintro ⟨y, hy, hxy⟩
    have hsub : x - y ∈ T := hker (x - y) (by rw [map_sub, hxy, sub_self])
    simpa only [sub_add_cancel] using T.add_mem hsub hy

/-- A conductor on the image of an ambient subring is a literal conductor
upstairs when the kernel is contained in the smaller subring. -/
theorem conductor_iff_map_conductor (T D : Subring R) (f : R →+* A)
    (hker : ∀ x : R, f x = 0 → x ∈ T) (c : R) :
    (∀ x ∈ D, c * x ∈ T) ↔ ∀ y ∈ D.map f, f c * y ∈ T.map f := by
  constructor
  · intro h y hy
    rcases hy with ⟨x, hx, rfl⟩
    exact ⟨c * x, h x hx, map_mul f c x⟩
  · intro h x hx
    apply (mem_iff_map_mem_of_kernel_subset T f hker (c * x)).mpr
    rw [map_mul]
    exact h (f x) ⟨x, hx, rfl⟩

/-- Quotient specialization uses ideal containment only; `T` need not be an
ideal and the quotient is taken by the actual ideal `I`. -/
theorem conductor_iff_quotient_conductor (T D : Subring R) (I : Ideal R)
    (hI : ∀ x ∈ I, x ∈ T) (c : R) :
    (∀ x ∈ D, c * x ∈ T) ↔
      ∀ y ∈ D.map (Ideal.Quotient.mk I),
        Ideal.Quotient.mk I c * y ∈ T.map (Ideal.Quotient.mk I) := by
  apply conductor_iff_map_conductor
  intro x hx
  exact hI x (Ideal.Quotient.eq_zero_iff_mem.mp hx)

section Localization

variable {K : Type*} [Field K]

/-- All inverse powers of one numerator give its entire localized principal
ideal, using an explicit power-denominator clearing property. -/
theorem conductor_of_inverse_powers (T B : Subring K) (p h : K) (hp : p ≠ 0)
    (hpower : ∀ n : ℕ, h / p ^ n ∈ T)
    (hclear : ∀ b ∈ B, ∃ n : ℕ, p ^ n * b ∈ T) :
    ∀ b ∈ B, h * b ∈ T := by
  intro b hb
  obtain ⟨n, hn⟩ := hclear b hb
  have hmem := T.mul_mem (hpower n) hn
  simpa only [← mul_assoc, div_mul_cancel₀ h (pow_ne_zero n hp)] using hmem

end Localization

end UnconditionalCounterexample.LocalAlgebra
