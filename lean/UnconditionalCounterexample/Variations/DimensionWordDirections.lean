import UnconditionalCounterexample.Variations.DimensionGradientEscape
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.RingTheory.Localization.Basic

/-!
# Directional derivatives of actual localized words

A residue-valued derivation is detected on the coordinate variables of the
polynomial localization. The relation defining each listed fraction identifies
its derivative with the quotient-rule formula in its residue field. Thus the
gradient estimates for the literal listed words give the directional escape
required by the conductor equality.
-/

namespace UnconditionalCounterexample.Variations

open MvPolynomial Filter
open scoped Topology

variable {K E σ B : Type*} [Field K] [NontriviallyNormedField E] [Algebra K E] [Fintype σ]
    [CommRing B] [Algebra K B] [Algebra (MvPolynomial σ K) B] [IsScalarTower K (MvPolynomial σ K) B]

/-- The actual quotient-rule gradient of a listed word with known numerator and denominator. -/
noncomputable def residueWordGradient (u : σ → E) (F H : MvPolynomial σ K) (a : ℕ) (l : σ) : E :=
  (aeval u (pderiv l (F^a)) * aeval u H - aeval u (F^a) * aeval u (pderiv l H)) /
    (aeval u H)^2

/-- A linear operator satisfying Leibniz for a residue evaluation differentiates a
polynomial via its coordinate derivatives, even at a point with extended residue field. -/
theorem apply_polynomial_of_leibniz (u : σ → E) (ev : B →ₐ[K] E)
    (hev : ∀ F : MvPolynomial σ K, ev (algebraMap _ B F) = aeval u F)
    (δ : B →ₗ[K] E)
    (hδ : ∀ x y, δ (x*y) = ev x * δ y + ev y * δ x) (f : MvPolynomial σ K) :
    δ (algebraMap _ B f) =
      ∑ i, aeval u (pderiv i f) * δ (algebraMap (MvPolynomial σ K) B (X i)) := by
  classical
  have h1 := hδ 1 1
  simp only [one_mul, map_one] at h1
  have hz : δ 1 = 0 := by linear_combination -h1
  induction f using MvPolynomial.induction_on with
  | C c =>
    rw [show algebraMap (MvPolynomial σ K) B (C c) = c • (1 : B) by
      rw [Algebra.smul_def, mul_one, IsScalarTower.algebraMap_apply K (MvPolynomial σ K) B]; rfl]
    simp [hz]
  | add f g hf hg => simp [hf, hg, add_mul, Finset.sum_add_distrib]
  | mul_X f j hf =>
    rw [map_mul, hδ, hev, hev, hf]
    simp [Derivation.leibniz, smul_eq_mul, Pi.single_apply, add_mul, Finset.sum_add_distrib,
      apply_ite, ite_mul, Finset.mul_sum, mul_assoc]

variable (M : Submonoid (MvPolynomial σ K)) [IsLocalization M B]

include M in
/-- A nonzero residue-valued derivation on the localization detects some coordinate. -/
theorem exists_coordinate_of_nonzero_leibniz (u : σ → E) (ev : B →ₐ[K] E)
    (hev : ∀ F : MvPolynomial σ K, ev (algebraMap _ B F) = aeval u F)
    (δ : B →ₗ[K] E) (hne : δ ≠ 0)
    (hδ : ∀ x y, δ (x*y) = ev x * δ y + ev y * δ x) :
    ∃ i, δ (algebraMap (MvPolynomial σ K) B (X i)) ≠ 0 := by
  by_contra! h
  apply hne
  have hpol (f : MvPolynomial σ K) : δ (algebraMap _ B f) = 0 := by
    rw [apply_polynomial_of_leibniz u ev hev δ hδ]
    simp [h]
  ext z
  obtain ⟨f, t, rfl⟩ := IsLocalization.exists_mk'_eq M z
  have he := congrArg δ (IsLocalization.mk'_spec B f t)
  rw [hδ, hpol, hpol, mul_zero, zero_add] at he
  exact (mul_eq_zero.mp he).resolve_left (((IsLocalization.map_units B t).map ev).ne_zero)

/-- On a listed fraction the linear operator is its gradient paired with the
coordinate vector of the operator. -/
theorem apply_word_of_leibniz (u : σ → E) (ev : B →ₐ[K] E)
    (hev : ∀ F : MvPolynomial σ K, ev (algebraMap _ B F) = aeval u F)
    (δ : B →ₗ[K] E)
    (hδ : ∀ x y, δ (x*y) = ev x * δ y + ev y * δ x)
    (F H : MvPolynomial σ K) (a : ℕ) (w : B)
    (hrel : algebraMap _ B (F^a) = algebraMap _ B H * w) (hH : aeval u H ≠ 0) :
    δ w = ∑ i, residueWordGradient u F H a i * δ (algebraMap (MvPolynomial σ K) B (X i)) := by
  classical
  have hw : ev w = aeval u (F^a) / aeval u H := by
    apply (eq_div_iff hH).mpr
    have heq := congrArg ev hrel
    simpa [hev, mul_comm] using heq.symm
  have heq := congrArg δ hrel
  rw [hδ, hev, hw, apply_polynomial_of_leibniz u ev hev δ hδ,
    apply_polynomial_of_leibniz u ev hev δ hδ] at heq
  apply (mul_left_cancel₀ (pow_ne_zero 2 hH))
  have hterm (i : σ) : (aeval u H)^2 *
      (residueWordGradient u F H a i * δ (algebraMap (MvPolynomial σ K) B (X i))) =
      aeval u H * (aeval u (pderiv i (F^a)) * δ (algebraMap (MvPolynomial σ K) B (X i))) -
      aeval u (F^a) * (aeval u (pderiv i H) * δ (algebraMap (MvPolynomial σ K) B (X i))) := by
    dsimp [residueWordGradient]
    field_simp
  rw [Finset.mul_sum]
  simp only [hterm, Finset.sum_sub_distrib, ← Finset.mul_sum]
  field_simp at heq
  linear_combination -heq

/-- Escaping actual gradients of the listed words give unbounded values for every
nonzero residue-valued derivation on the localized polynomial algebra. -/
theorem unbounded_leibniz_of_word_gradients (M : Submonoid (MvPolynomial σ K)) [IsLocalization M B]
    (u : σ → E) (ev : B →ₐ[K] E)
    (hev : ∀ F : MvPolynomial σ K, ev (algebraMap _ B F) = aeval u F) (T : Subring B)
    (F H : ℕ → MvPolynomial σ K) (a : ℕ → ℕ) (w : ℕ → T)
    (hrel : ∀ n, algebraMap _ B (F n ^ a n) = algebraMap _ B (H n) * (w n : B))
    (hH : ∀ n, aeval u (H n) ≠ 0)
    (hgrad : ∀ L : (σ → E) →L[E] E, L ≠ 0 →
      Tendsto (fun n ↦ ‖L (residueWordGradient u (F n) (H n) (a n))‖) atTop atTop)
    (δ : B →ₗ[K] E) (hne : δ ≠ 0)
    (hδ : ∀ x y, δ (x*y) = ev x * δ y + ev y * δ x) :
    ∀ R : ℝ, ∃ x ∈ T, R < ‖δ x‖ := by
  classical
  let v i := δ (algebraMap (MvPolynomial σ K) B (X i))
  let L : (σ → E) →L[E] E := ∑ i, v i • ContinuousLinearMap.proj i
  have happ (z : σ → E) : L z = ∑ i, z i * v i := by simp [L, mul_comm]
  have hneL : L ≠ 0 := by
    obtain ⟨i, hi⟩ := exists_coordinate_of_nonzero_leibniz M u ev hev δ hne hδ
    intro hz
    have hv := congrArg (fun f : (σ → E) →L[E] E ↦ f (Pi.single i 1)) hz
    rw [happ] at hv
    simp [v, Pi.single_apply, ite_mul, hi] at hv
  intro R
  obtain ⟨n, hn⟩ := ((hgrad L hneL).eventually_gt_atTop R).exists
  refine ⟨w n, (w n).property, ?_⟩
  rw [apply_word_of_leibniz u ev hev δ hδ _ _ _ _ (hrel n) (hH n)]
  simpa only [happ, v] using hn

end UnconditionalCounterexample.Variations
