import UnconditionalCounterexample.Variations.DimensionRecoveryGenerators
import Mathlib.RingTheory.Localization.Ideal

namespace UnconditionalCounterexample.Variations

open Polynomial

/-- Encode a finite generating family into distinct coefficients. -/
noncomputable def schedulePolynomial {R : Type*} [CommRing R] {n : ℕ} (g : Fin n → R) : R[X] :=
  ∑ j : Fin n, monomial j.val (g j)

theorem schedulePolynomial_content {R : Type*} [CommRing R] {n : ℕ} (g : Fin n → R) :
    (schedulePolynomial g).contentIdeal = Ideal.span (Set.range g) := by
  classical
  have hc (j : Fin n) : (schedulePolynomial g).coeff j = g j := by
    simp [schedulePolynomial, finsetSum_coeff, coeff_monomial, Fin.val_inj]
  apply le_antisymm
  · rw [contentIdeal_def, Ideal.span_le]
    intro x hx
    obtain ⟨e, _, rfl⟩ := Polynomial.mem_coeffs_iff.mp hx
    by_cases he : e < n
    · rw [show (schedulePolynomial g).coeff e = _ from hc ⟨e,he⟩]
      exact Ideal.subset_span ⟨_,rfl⟩
    · have hz (j : Fin n) : (j : ℕ) ≠ e := fun hj ↦ he (hj ▸ j.isLt)
      simp [schedulePolynomial, finsetSum_coeff, coeff_monomial, hz]
  · rw [Ideal.span_le]
    rintro _ ⟨j,rfl⟩
    rw [← hc j]
    exact coeff_mem_contentIdeal _ _

theorem schedulePolynomial_map {R S : Type*} [CommRing R] [CommRing S] {n : ℕ}
    (g : Fin n → R) (f : R →+* S) : (schedulePolynomial g).map f = schedulePolynomial (f ∘ g) := by
  simp [schedulePolynomial, Polynomial.map_sum]

open MvPolynomial in
theorem localized_schedule_content {K σ ι : Type*} [NontriviallyNormedField K]
    {E : ι → Type*} [∀ i, NontriviallyNormedField (E i)] [∀ i, NormedAlgebra K (E i)]
    {u : ∀ i, σ → E i} (G : RecoveryGenerators (K := K) u)
    {A : Type*} [CommRing A] [Algebra K A] [Algebra (MvPolynomial σ K) A]
    (M : Submonoid (MvPolynomial σ K)) [IsLocalization M A]
    (ev : ∀ i, A →ₐ[K] E i) (hev : ∀ i (F : MvPolynomial σ K), ev i (algebraMap _ A F) = MvPolynomial.aeval (u i) F)
    (c : Kˣ) : (schedulePolynomial (fun j ↦ algebraMap K A (c : K) * algebraMap _ A (G.gen j))).contentIdeal =
    ⨅ i, RingHom.ker (ev i) := by
  classical
  let I := ⨅ i, RingHom.ker (ev i)
  let φ := algebraMap (MvPolynomial σ K) A
  have hI : I.under (MvPolynomial σ K) = ⨅ i, RingHom.ker (MvPolynomial.aeval (R := K) (u i)).toRingHom := by
    ext z
    change φ z ∈ ⨅ i, RingHom.ker (ev i) ↔ _
    simp only [Ideal.mem_iInf, RingHom.mem_ker, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, φ, hev]
  rw [schedulePolynomial_content]
  have hid : Ideal.span (Set.range (fun j ↦ φ (G.gen j))) = I := by
    rw [← IsLocalization.map_under M A I, hI, ← G.span, Ideal.map_span, Set.range_comp']
  change Ideal.span _ = I
  rw [← hid]
  apply le_antisymm <;> rw [Ideal.span_le]
  · rintro _ ⟨j,rfl⟩
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨j,rfl⟩)
  · rintro _ ⟨j,rfl⟩
    let J := Ideal.span (Set.range fun j ↦ algebraMap K A (c : K) * φ (G.gen j))
    have hh := J.mul_mem_left (algebraMap K A (↑(c⁻¹) : K)) (Ideal.subset_span (Set.mem_range_self j))
    change φ (G.gen j) ∈ J
    simpa only [← mul_assoc, ← map_mul, Units.inv_mul, map_one, one_mul] using hh

end UnconditionalCounterexample.Variations
