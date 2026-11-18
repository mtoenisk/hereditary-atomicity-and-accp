import UnconditionalCounterexample.LocalAlgebra.ScaledTransferConductor
import UnconditionalCounterexample.SingleLocalInterpolation

/-!
# Transfer for the single guard argument

Section 8.2 uses the literal g=p^(2s)(t-beta), with beta the only argument.
Its normalized linear factor has constant one and the coefficient scalar is
p^(2s)(-beta). The same exact two-term algebra and scalar saturation as in
the paired case then give a power of this single surviving linear factor.
-/

namespace UnconditionalCounterexample.LocalAlgebra

open Polynomial Filter

variable {K E : Type*} [Field K] [Field E]

theorem scaled_single_eq_linear (ι : K →+* E) (π β : K) (t : E) (s : ℕ) :
    ι π ^ (2 * s) * (t - ι β) =
      ι π ^ s * (ι π ^ s * t) - ι (π ^ (2 * s) * β) := by
  rw [Nat.mul_comm 2 s, pow_mul]
  simp only [map_mul, map_pow]
  ring

theorem scaled_single_mem_scaledPolynomialRing
    (O : Subring K) (ι : K →+* E) (π β : K)
    (hπ : π ∈ O) (hβ : β ∈ O) (t : E) (s : ℕ) :
    ι π ^ (2 * s) * (t - ι β) ∈ scaledPolynomialRing O ι (ι π ^ s * t) := by
  rw [scaled_single_eq_linear]
  apply (scaledPolynomialRing O ι (ι π ^ s * t)).sub_mem
  · have hsc := scalar_mem_scaledPolynomialRing O ι (ι π ^ s * t) (O.pow_mem hπ s)
    rw [map_pow] at hsc
    exact (scaledPolynomialRing O ι _).mul_mem hsc (coordinate_mem_scaledPolynomialRing O ι _)
  · exact scalar_mem_scaledPolynomialRing O ι _ (O.mul_mem (O.pow_mem hπ _) hβ)

/-- Actual one-point coefficient estimates give the two-term transfer at the
same beta, with the manuscript's p^(2s) normalization. -/
theorem scaled_single_word_transfer
    (O : Subring K) (ι : K →+* E) (t : E) (π c β η : K) (d s i a : ℕ)
    (F H : K[X]) (hπ : π ≠ 0) (hπO : π ∈ O) (hβ : β ≠ 0) (hβO : β ∈ O)
    (hc : c ≠ 0) (hcinv : c⁻¹ ∈ O) (ha : 0 < a) (hH : H.eval₂ ι t ≠ 0)
    (herror : ∀ j, (((F - SingleLocalInterpolation.localTarget β η d c).comp
      (C ((π ^ s)⁻¹) * X)).coeff j / c) / π ^ i ∈ O)
    (hJ : ∀ j, (((SingleLocalInterpolation.fixedRemainder β η d).comp
      (C ((π ^ s)⁻¹) * X)).coeff j / c) / π ^ i ∈ O)
    (hden : ∀ j, ((H.comp (C ((π ^ s)⁻¹) * X)).coeff j / c) / π ^ i ∈ O) :
    ∃ U V : scaledPolynomialRing O ι (ι π ^ s * t),
      (ι π ^ (2 * s) * (t - ι β)) ^ a =
        ι π ^ i * ((U : E) + (V : E) * (F.eval₂ ι t ^ a / H.eval₂ ι t)) := by
  let g : scaledPolynomialRing O ι (ι π ^ s * t) :=
    ⟨ι π ^ (2 * s) * (t - ι β), scaled_single_mem_scaledPolynomialRing O ι π β hπO hβO t s⟩
  apply word_transfer_of_scaled_coefficients O ι t π c (π ^ (2 * s) * (-β)) s i a F
    (SingleLocalInterpolation.normalizedVanishing β) (SingleLocalInterpolation.fixedRemainder β η d)
    H hπ hπO (O.mul_mem (O.pow_mem hπO _) (O.neg_mem hβO)) hc hcinv ha hH g _ herror hJ hden
  change ι π ^ (2 * s) * (t - ι β) = _
  simp only [SingleLocalInterpolation.normalizedVanishing, eval₂_sub, eval₂_one,
    eval₂_mul, eval₂_C, eval₂_X, map_mul, map_pow, map_neg, map_inv₀]
  have hβE : ι β ≠ 0 := by simpa only [map_zero] using ι.injective.ne hβ
  field_simp
  ring

/-- Literal single-factor stage identities imply the entire conductor power. -/
theorem padic_single_conductor_power_of_word_transfers
    (p : ℕ) [Fact p.Prime] (s R : ℕ) (β : ℚ_[p]) (hβ : β ∈ PadicInt.subring p)
    (T B : Subring (RatFunc ℚ_[p]))
    (hO : ∀ c ∈ PadicInt.subring p, RatFunc.C c ∈ T)
    (ht : RatFunc.C (p : ℚ_[p]) ^ s * RatFunc.X ∈ T)
    (hinv : (RatFunc.C (p : ℚ_[p]))⁻¹ ∈ B)
    (hclear : ∀ b ∈ B, ∃ n : ℕ, RatFunc.C (p : ℚ_[p]) ^ n * b ∈ T)
    (hwords : ∀ k : ℕ, ∃ (i e : ℕ) (w : RatFunc ℚ_[p]), k ≤ i ∧ e ≤ R ∧ w ∈ T ∧
      ∃ u v : padicScaledPolynomialRing p s,
        (RatFunc.C (p : ℚ_[p]) ^ (2 * s) * (RatFunc.X - RatFunc.C β)) ^ e =
        RatFunc.C (p : ℚ_[p]) ^ i * ((u : RatFunc ℚ_[p]) + (v : RatFunc ℚ_[p]) * w)) :
    ∀ b ∈ B, (RatFunc.X - RatFunc.C β) ^ R * b ∈ T := by
  let A := padicScaledPolynomialRing p s
  let π : A := ⟨RatFunc.C (p : ℚ_[p]), scalar_mem_scaledPolynomialRing
    (PadicInt.subring p) RatFunc.C _ (by simp)⟩
  let g : A := ⟨RatFunc.C (p : ℚ_[p]) ^ (2 * s) * (RatFunc.X - RatFunc.C β),
    scaled_single_mem_scaledPolynomialRing (PadicInt.subring p) RatFunc.C (p : ℚ_[p]) β
      (by simp) hβ RatFunc.X s⟩
  have hπ : (π : RatFunc ℚ_[p]) ≠ 0 := by
    change RatFunc.C (p : ℚ_[p]) ≠ 0
    exact (_root_.map_ne_zero RatFunc.C).mpr
      (Nat.cast_ne_zero.mpr (show p.Prime from Fact.out).ne_zero)
  exact conductor_power_of_word_transfers A T B (padicScaledPolynomialRing_le p s T hO ht)
    π g (RatFunc.X - RatFunc.C β) s R hπ hinv rfl hclear hwords

theorem padic_single_conductor_power_of_eventual_word_transfers
    (p : ℕ) [Fact p.Prime] (s R : ℕ) (β : ℚ_[p]) (hβ : β ∈ PadicInt.subring p)
    (T B : Subring (RatFunc ℚ_[p]))
    (hO : ∀ c ∈ PadicInt.subring p, RatFunc.C c ∈ T)
    (ht : RatFunc.C (p : ℚ_[p]) ^ s * RatFunc.X ∈ T)
    (hinv : (RatFunc.C (p : ℚ_[p]))⁻¹ ∈ B)
    (hclear : ∀ b ∈ B, ∃ n : ℕ, RatFunc.C (p : ℚ_[p]) ^ n * b ∈ T)
    (stage e : ℕ → ℕ) (F H : ℕ → ℚ_[p][X]) (hstage : Tendsto stage atTop atTop)
    (hwords : ∀ᶠ n in atTop, e n ≤ R ∧
      ((F n : RatFunc ℚ_[p]) ^ e n / (H n : RatFunc ℚ_[p])) ∈ T ∧
      ∃ u v : padicScaledPolynomialRing p s,
        (RatFunc.C (p : ℚ_[p]) ^ (2 * s) * (RatFunc.X - RatFunc.C β)) ^ e n =
        RatFunc.C (p : ℚ_[p]) ^ stage n * ((u : RatFunc ℚ_[p]) +
          (v : RatFunc ℚ_[p]) * ((F n : RatFunc ℚ_[p]) ^ e n / (H n : RatFunc ℚ_[p])))) :
    ∀ b ∈ B, (RatFunc.X - RatFunc.C β) ^ R * b ∈ T := by
  apply padic_single_conductor_power_of_word_transfers p s R β hβ T B hO ht hinv hclear
  intro k
  have hlarge : ∀ᶠ n in atTop, k ≤ stage n := hstage.eventually (eventually_ge_atTop k)
  obtain ⟨n, hn, he, hw, huv⟩ := (hlarge.and hwords).exists
  exact ⟨stage n, e n, _, hn, he, hw, huv⟩

end UnconditionalCounterexample.LocalAlgebra
