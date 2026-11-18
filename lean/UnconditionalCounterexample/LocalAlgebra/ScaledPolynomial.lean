import UnconditionalCounterexample.LocalAlgebra.WordTransfer
import Mathlib.RingTheory.Polynomial.Subring
import UnconditionalCounterexample.LocalStageSelection
import Mathlib.FieldTheory.RatFunc.AsPolynomial

/-!
# Actual transfer in the scaled p-adic polynomial ring

The local coefficient estimate and transfer identity of Proposition 3.1(4) are combined in
`LocalAlgebra.signed_word_transfer_in_padic_scaled_ring`.

Coefficient estimates for the selected polynomial, its fixed interpolation
remainder, and the word denominator produce actual elements of
`A_s = ℤ_p[p^s t]`. Integral roots prove membership of
`g = p^(2*s) (t-alpha)(t-beta)` and its normalizing scalar. The signed constant
has integral inverse. The resulting equality `g^a = p^i (u + v*w)` uses the
same selected coefficients and the same word as the stage hypotheses.

The endpoint works in the literal subring of `RatFunc ℚ_[p]`; no transfer
identity, numerator membership, or divisibility conclusion is assumed.
The simultaneous recursive constructor must still supply the prepared stage
conditions for its actual data.
-/

namespace UnconditionalCounterexample.LocalAlgebra

open Polynomial

variable {K E : Type*} [Field K] [Field E]

/-- The polynomial subring over the integral coefficients at the scaled
coordinate. In the application the coordinate is p^s t in Q_p(t). -/
noncomputable def scaledPolynomialRing (O : Subring K) (ι : K →+* E) (z : E) : Subring E :=
  (eval₂RingHom (ι.comp O.subtype) z).range

theorem scalar_mem_scaledPolynomialRing (O : Subring K) (ι : K →+* E) (z : E)
    {c : K} (hc : c ∈ O) : ι c ∈ scaledPolynomialRing O ι z :=
  ⟨C ⟨c, hc⟩, by simp⟩

theorem coordinate_mem_scaledPolynomialRing (O : Subring K) (ι : K →+* E) (z : E) :
    z ∈ scaledPolynomialRing O ι z :=
  ⟨X, by simp⟩

/-- A coefficientwise congruence gives an actual quotient in the evaluated
integral polynomial ring, including when the polynomial is zero. -/
theorem evaluated_eq_mul_of_integral_coefficients (O : Subring K) (ι : K →+* E)
    (z : E) (P : K[X]) (d : K) (hd : d ≠ 0) (h : ∀ j, P.coeff j / d ∈ O) :
    ∃ v : scaledPolynomialRing O ι z, P.eval₂ ι z = ι d * (v : E) := by
  classical
  let Q := C d⁻¹ * P
  have hQ : (↑Q.coeffs : Set K) ⊆ O := by
    intro c hc
    obtain ⟨j, _, rfl⟩ := mem_coeffs_iff.mp hc
    change (C d⁻¹ * P).coeff j ∈ O
    rw [coeff_C_mul, mul_comm, ← div_eq_mul_inv]
    exact h j
  let V := Q.toSubring O hQ
  have he : V.eval₂ (ι.comp O.subtype) z = Q.eval₂ ι z := by
    rw [← eval₂_map, map_toSubring]
  refine ⟨⟨_, ⟨V, rfl⟩⟩, ?_⟩
  change P.eval₂ ι z = ι d * V.eval₂ (ι.comp O.subtype) z
  rw [he]
  simp [Q, hd]

/-- Undo the substitution Z/p^s at the scaled coordinate. -/
theorem eval_scaled_comp (ι : K →+* E) (t : E) (π : K) (hπ : π ≠ 0)
    (s : ℕ) (F : K[X]) :
    (F.comp (C ((π ^ s)⁻¹) * X)).eval₂ ι (ι π ^ s * t) = F.eval₂ ι t := by
  rw [eval₂_comp]
  simp [hπ]

/-- The normalized, rescaled polynomial evaluates to a multiple of the
requested precision in the literal ring of integral polynomials at p^s t. -/
theorem scaled_evaluation_of_coefficients (O : Subring K) (ι : K →+* E) (t : E)
    (π c : K) (s i : ℕ) (F : K[X]) (hπ : π ≠ 0)
    (h : ∀ j, (((F.comp (C ((π ^ s)⁻¹) * X)).coeff j) / c) / π ^ i ∈ O) :
    ∃ v : scaledPolynomialRing O ι (ι π ^ s * t),
      F.eval₂ ι t / ι c = ι π ^ i * (v : E) := by
  have hc (j : ℕ) :
      (C c⁻¹ * F.comp (C ((π ^ s)⁻¹) * X)).coeff j / π ^ i ∈ O := by
    rw [coeff_C_mul, mul_comm, ← div_eq_mul_inv]
    exact h j
  obtain ⟨v, hv⟩ := evaluated_eq_mul_of_integral_coefficients O ι
    (ι π ^ s * t) _ (π ^ i) (pow_ne_zero _ hπ) hc
  refine ⟨v, ?_⟩
  rw [eval₂_mul, eval₂_C, eval_scaled_comp ι t π hπ, map_inv₀, map_pow] at hv
  simpa only [div_eq_mul_inv, mul_comm (F.eval₂ ι t)] using hv

theorem scaled_pair_eq_product (ι : K →+* E) (π α β : K) (t : E) (s : ℕ) :
    ι π ^ (2 * s) * ((t - ι α) * (t - ι β)) =
      (ι π ^ s * t - ι (π ^ s * α)) * (ι π ^ s * t - ι (π ^ s * β)) := by
  rw [Nat.mul_comm 2 s, pow_mul]
  simp only [map_mul, map_pow]
  ring

theorem scaled_pair_mem_scaledPolynomialRing
    (O : Subring K) (ι : K →+* E) (π α β : K)
    (hπ : π ∈ O) (hα : α ∈ O) (hβ : β ∈ O) (t : E) (s : ℕ) :
    ι π ^ (2 * s) * ((t - ι α) * (t - ι β)) ∈
      scaledPolynomialRing O ι (ι π ^ s * t) := by
  rw [scaled_pair_eq_product]
  apply (scaledPolynomialRing O ι (ι π ^ s * t)).mul_mem
  · exact (scaledPolynomialRing O ι (ι π ^ s * t)).sub_mem
      (coordinate_mem_scaledPolynomialRing O ι _)
      (scalar_mem_scaledPolynomialRing O ι _ (O.mul_mem (O.pow_mem hπ s) hα))
  · exact (scaledPolynomialRing O ι (ι π ^ s * t)).sub_mem
      (coordinate_mem_scaledPolynomialRing O ι _)
      (scalar_mem_scaledPolynomialRing O ι _ (O.mul_mem (O.pow_mem hπ s) hβ))

theorem scaled_pair_constant_mem (O : Subring K) (π α β : K)
    (hπ : π ∈ O) (hα : α ∈ O) (hβ : β ∈ O) (s : ℕ) :
    π ^ (2 * s) * (α * β) ∈ O :=
  O.mul_mem (O.pow_mem hπ _) (O.mul_mem hα hβ)

theorem scaled_pair_constant_image_mem (O : Subring K) (ι : K →+* E) (π α β : K)
    (hπ : π ∈ O) (hα : α ∈ O) (hβ : β ∈ O) (t : E) (s : ℕ) :
    ι (π ^ (2 * s) * (α * β)) ∈ scaledPolynomialRing O ι (ι π ^ s * t) :=
  scalar_mem_scaledPolynomialRing O ι _ (scaled_pair_constant_mem O π α β hπ hα hβ s)


/-- Integral normalized error and remainder coefficients give the actual
word-transfer identity in the evaluated scaled polynomial ring. -/
theorem word_transfer_of_scaled_coefficients
    (O : Subring K) (ι : K →+* E) (t : E) (π c lam : K) (s i a : ℕ)
    (F ell J H : K[X]) (hπ : π ≠ 0) (hπO : π ∈ O) (hlam : lam ∈ O)
    (hc : c ≠ 0) (hcinv : c⁻¹ ∈ O) (ha : 0 < a) (hH : H.eval₂ ι t ≠ 0)
    (g : scaledPolynomialRing O ι (ι π ^ s * t))
    (hg : (g : E) = ι lam * ell.eval₂ ι t)
    (herror : ∀ j, (((F - (C c * ell + J)).comp
      (C ((π ^ s)⁻¹) * X)).coeff j / c) / π ^ i ∈ O)
    (hJ : ∀ j, ((J.comp (C ((π ^ s)⁻¹) * X)).coeff j / c) / π ^ i ∈ O)
    (hden : ∀ j, ((H.comp (C ((π ^ s)⁻¹) * X)).coeff j / c) / π ^ i ∈ O) :
    ∃ u v : scaledPolynomialRing O ι (ι π ^ s * t),
      (g : E) ^ a = ι π ^ i * ((u : E) + (v : E) * (F.eval₂ ι t ^ a / H.eval₂ ι t)) := by
  let A := scaledPolynomialRing O ι (ι π ^ s * t)
  let piA : A := ⟨ι π, scalar_mem_scaledPolynomialRing O ι _ hπO⟩
  let scaleA : A := ⟨ι lam, scalar_mem_scaledPolynomialRing O ι _ hlam⟩
  obtain ⟨U, hU⟩ := scaled_evaluation_of_coefficients O ι t π c s i
    (F - (C c * ell + J)) hπ herror
  obtain ⟨V, hV⟩ := scaled_evaluation_of_coefficients O ι t π c s i J hπ hJ
  have hcE : ι c ≠ 0 := by simpa only [map_zero] using ι.injective.ne hc
  have hF : F.eval₂ ι t / ι c = ell.eval₂ ι t + ι π ^ i * ((U : E) + (V : E)) := by
    calc
      F.eval₂ ι t / ι c =
        (F - (C c * ell + J)).eval₂ ι t / ι c + (C c * ell + J).eval₂ ι t / ι c := by
          rw [eval₂_sub]
          ring
      _ = ι π ^ i * (U : E) + (ι c * ell.eval₂ ι t + J.eval₂ ι t) / ι c := by
          rw [hU, eval₂_add, eval₂_mul, eval₂_C]
      _ = ell.eval₂ ι t + ι π ^ i * ((U : E) + (V : E)) := by
          rw [add_div, mul_div_cancel_left₀ _ hcE, hV]
          ring
  let f : A := g + piA ^ i * (scaleA * (U + V))
  have hf : (f : E) = ι lam * F.eval₂ ι t / ι c := by
    change (g : E) + ι π ^ i * (ι lam * ((U : E) + (V : E))) = _
    rw [hg, mul_div_assoc, hF]
    ring
  have hcong : piA ^ i ∣ f - g := by
    refine ⟨scaleA * (U + V), ?_⟩
    simp only [f, add_sub_cancel_left]
  exact exists_word_transfer_coefficients A piA f g (F.eval₂ ι t) (H.eval₂ ι t)
    (F.eval₂ ι t ^ a / H.eval₂ ι t) (ι lam) (ι c) i a ha hcE hH
    scaleA.property (by simpa only [map_inv₀] using
      scalar_mem_scaledPolynomialRing O ι (ι π ^ s * t) hcinv)
    hf rfl hcong (scaled_evaluation_of_coefficients O ι t π c s i H hπ hden)

/-- The quadratic normalization and fixed remainder give the manuscript's
literal scaled pair, with ring membership derived from the integral roots. -/
theorem scaled_pair_word_transfer
    (O : Subring K) (ι : K →+* E) (t : E) (π c α β u v : K) (d s i a : ℕ)
    (F H : K[X]) (hπ : π ≠ 0) (hπO : π ∈ O) (hα : α ≠ 0) (hβ : β ≠ 0)
    (hαO : α ∈ O) (hβO : β ∈ O) (hc : c ≠ 0) (hcinv : c⁻¹ ∈ O)
    (ha : 0 < a) (hH : H.eval₂ ι t ≠ 0)
    (herror : ∀ j, (((F - LocalInterpolation.localTarget α β u v d c).comp
      (C ((π ^ s)⁻¹) * X)).coeff j / c) / π ^ i ∈ O)
    (hJ : ∀ j, (((LocalInterpolation.fixedRemainder α β u v d).comp
      (C ((π ^ s)⁻¹) * X)).coeff j / c) / π ^ i ∈ O)
    (hden : ∀ j, ((H.comp (C ((π ^ s)⁻¹) * X)).coeff j / c) / π ^ i ∈ O) :
    ∃ U V : scaledPolynomialRing O ι (ι π ^ s * t),
      (ι π ^ (2 * s) * ((t - ι α) * (t - ι β))) ^ a =
        ι π ^ i * ((U : E) + (V : E) * (F.eval₂ ι t ^ a / H.eval₂ ι t)) := by
  let g : scaledPolynomialRing O ι (ι π ^ s * t) :=
    ⟨ι π ^ (2 * s) * ((t - ι α) * (t - ι β)),
      scaled_pair_mem_scaledPolynomialRing O ι π α β hπO hαO hβO t s⟩
  apply word_transfer_of_scaled_coefficients O ι t π c (π ^ (2 * s) * (α * β)) s i a F
    (LocalInterpolation.normalizedVanishing α β) (LocalInterpolation.fixedRemainder α β u v d)
    H hπ hπO (scaled_pair_constant_mem O π α β hπO hαO hβO s) hc hcinv ha hH g _
    herror hJ hden
  change ι π ^ (2 * s) * ((t - ι α) * (t - ι β)) = _
  simp only [LocalInterpolation.normalizedVanishing, eval₂_mul, eval₂_C, eval₂_sub,
    eval₂_X, map_mul, map_pow, map_inv₀]
  have hαE : ι α ≠ 0 := by simpa only [map_zero] using ι.injective.ne hα
  have hβE : ι β ≠ 0 := by simpa only [map_zero] using ι.injective.ne hβ
  field_simp

/-- The prepared coefficient ball and the fixed J/H clearing imply the
actual scaled-ring transfer for the same chosen full coefficient vector. -/
theorem word_transfer_of_local_conditions {W : Type*}
    (p : ℕ) [Fact p.Prime] (ι : ℚ_[p] →+* E) (t : E)
    (n stage : ℕ) (hn : 2 < n + 1) (c : ℚ_[p])
    (hc : c ≠ 0) (hcinv : c⁻¹ ∈ PadicInt.subring p)
    (q : Fin n → ℚ_[p]) (x B v : Bool → ℚ_[p]) (kv : Bool → ℕ)
    (hx : ∀ b, x b ≠ 0) (hxO : ∀ b, x b ∈ PadicInt.subring p)
    (ws : Finset W) (H : W → ℚ_[p][X]) (a : W → ℕ)
    (hclear : LocalStageSelection.ClearedAtPrime p stage c
      (LocalInterpolation.fixedRemainder (x false) (x true) (B false * v false)
        (B true * v true) (n + 1)) ws H)
    (hcond : LocalStageSelection.ConditionsAtPrime p n stage c
      (fun j => (LocalInterpolation.localTarget (x false) (x true) (B false * v false)
        (B true * v true) (n + 1) c).coeff (j.val + 1)) q x B v kv ws H a)
    (s : ℕ) (hs : s ≤ stage) (w : W) (hw : w ∈ ws)
    (ha : 0 < a w) (hH : (H w).eval₂ ι t ≠ 0) :
    ∃ U V : scaledPolynomialRing (PadicInt.subring p) ι (ι (p : ℚ_[p]) ^ s * t),
      (ι (p : ℚ_[p]) ^ (2 * s) * ((t - ι (x false)) * (t - ι (x true)))) ^ a w =
        ι (p : ℚ_[p]) ^ stage * ((U : E) + (V : E) *
          ((ShiftedEisenstein.monicFamily n c q).eval₂ ι t ^ a w / (H w).eval₂ ι t)) := by
  apply scaled_pair_word_transfer (PadicInt.subring p) ι t (p : ℚ_[p]) c
    (x false) (x true) (B false * v false) (B true * v true) (n + 1) s stage (a w)
    (ShiftedEisenstein.monicFamily n c q) (H w)
    (Nat.cast_ne_zero.mpr (show p.Prime from Fact.out).ne_zero) (by simp)
    (hx false) (hx true) (hxO false) (hxO true) hc hcinv ha hH
    ?_ ((hclear s hs).1) ((hclear s hs).2 w hw)
  intro j
  rw [← LocalStageSelection.localTarget_eq_monicFamily _ _ _ _ n c (hx false) (hx true) hn]
  have h := hcond.2.2 s hs j
  rw [coeff_C_mul, mul_comm c⁻¹, ← div_eq_mul_inv] at h
  exact h

end UnconditionalCounterexample.LocalAlgebra

namespace UnconditionalCounterexample.SignedConstant

theorem constant_inv_eq {ι : Type*} [Fintype ι]
    (p : ι → ℕ) (N : ι → ℕ) (d : ℕ) :
    (constant p N d)⁻¹ = (denominator p N : ℚ) * (-1) ^ d := by
  simp only [constant, div_eq_mul_inv, mul_inv_rev, inv_inv, ← inv_pow, inv_neg, inv_one]

theorem constant_inv_mem_padicInt {ι : Type*} [Fintype ι]
    (p : ι → ℕ) (N : ι → ℕ) (d q : ℕ) [Fact q.Prime] :
    (constant p N d : ℚ_[q])⁻¹ ∈ PadicInt.subring q := by
  rw [← Rat.cast_inv, constant_inv_eq]
  simp only [Rat.cast_mul, Rat.cast_natCast, Rat.cast_pow, Rat.cast_neg, Rat.cast_one]
  exact (PadicInt.subring q).mul_mem (by simp)
    ((PadicInt.subring q).pow_mem ((PadicInt.subring q).neg_mem (PadicInt.subring q).one_mem) d)

end UnconditionalCounterexample.SignedConstant


namespace UnconditionalCounterexample.LocalAlgebra

open Polynomial

/-- The literal ring of p-adic integral polynomials in `p^s t`. -/
noncomputable abbrev padicScaledPolynomialRing (p : ℕ) [Fact p.Prime] (s : ℕ) :
    Subring (RatFunc ℚ_[p]) :=
  scaledPolynomialRing (PadicInt.subring p) RatFunc.C (RatFunc.C (p : ℚ_[p]) ^ s * RatFunc.X)

theorem eval₂_C_X_eq_coe {K : Type*} [Field K] (P : K[X]) :
    P.eval₂ RatFunc.C RatFunc.X = (P : RatFunc K) := by
  exact RatFunc.aeval_X_left_eq_algebraMap P

/-- The signed constant discharges inverse integrality; polynomial evaluation
at the actual rational-function variable discharges the denominator embedding.
This gives Proposition 3.1(4) for the same coefficients selected at the stage. -/
theorem signed_word_transfer_in_padic_scaled_ring {ι W : Type*} [Fintype ι]
    (processed : ι → ℕ) (hp : ∀ i, (processed i).Prime) (N : ι → ℕ)
    (p : ℕ) [Fact p.Prime] (n stage : ℕ) (hn : 2 < n + 1) :
    let c : ℚ_[p] := SignedConstant.constant processed N (n + 1)
    ∀ (q : Fin n → ℚ_[p]) (x B v : Bool → ℚ_[p]) (kv : Bool → ℕ),
    (∀ b, x b ≠ 0) → (∀ b, x b ∈ PadicInt.subring p) →
    ∀ (ws : Finset W) (H : W → ℚ_[p][X]) (a : W → ℕ),
    LocalStageSelection.ClearedAtPrime p stage c
      (LocalInterpolation.fixedRemainder (x false) (x true) (B false * v false)
        (B true * v true) (n + 1)) ws H →
    LocalStageSelection.ConditionsAtPrime p n stage c
      (fun j => (LocalInterpolation.localTarget (x false) (x true) (B false * v false)
        (B true * v true) (n + 1) c).coeff (j.val + 1)) q x B v kv ws H a →
    ∀ (s : ℕ), s ≤ stage → ∀ w ∈ ws, 0 < a w → H w ≠ 0 →
    ∃ U V : padicScaledPolynomialRing p s,
      (RatFunc.C (p : ℚ_[p]) ^ (2 * s) *
        ((RatFunc.X - RatFunc.C (x false)) * (RatFunc.X - RatFunc.C (x true)))) ^ a w =
        RatFunc.C (p : ℚ_[p]) ^ stage * ((U : RatFunc ℚ_[p]) + (V : RatFunc ℚ_[p]) *
          ((ShiftedEisenstein.monicFamily n c q : RatFunc ℚ_[p]) ^ a w / (H w : RatFunc ℚ_[p]))) := by
  dsimp only
  intro q x B v kv hx hxO ws H a hclear hcond s hs w hw ha hH
  have hc : (SignedConstant.constant processed N (n + 1) : ℚ_[p]) ≠ 0 :=
    Rat.cast_ne_zero.mpr (SignedConstant.constant_ne_zero processed hp N (n + 1))
  have hHeval : (H w).eval₂ RatFunc.C RatFunc.X ≠ (0 : RatFunc ℚ_[p]) := by
    rw [eval₂_C_X_eq_coe]
    exact RatFunc.algebraMap_ne_zero hH
  simpa only [eval₂_C_X_eq_coe] using
    word_transfer_of_local_conditions p RatFunc.C RatFunc.X n stage hn
      (SignedConstant.constant processed N (n + 1) : ℚ_[p]) hc
      (SignedConstant.constant_inv_mem_padicInt processed N (n + 1) p)
      q x B v kv hx hxO ws H a hclear hcond s hs w hw ha hHeval

end UnconditionalCounterexample.LocalAlgebra
