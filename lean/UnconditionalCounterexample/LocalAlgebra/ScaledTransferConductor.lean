import UnconditionalCounterexample.LocalAlgebra.ScaledPolynomial

/-!
# Conductor powers from actual scaled-polynomial transfers

In the exact-transfer argument of Lemma 6.1, integral scalars
and the scaled coordinate give Zp[p^s t] inside the actual target subring.
The literal two-term transfer identities, bounded exponents and arbitrarily
late stages then give L^R times the entire ambient pole algebra inside that
subring. The ordinary algebraic scalar-clearing hypothesis stays explicit.
The finite-stage producer is signed_word_transfer_in_padic_scaled_ring.
-/

namespace UnconditionalCounterexample.LocalAlgebra

open Polynomial Filter

variable {K E : Type*} [Field K] [Field E]

/-- The actual integral polynomial image lies in any subring containing its
integral scalars and its scaled coordinate. -/
theorem scaledPolynomialRing_le (O : Subring K) (ι : K →+* E) (z : E)
    (T : Subring E) (hO : ∀ c ∈ O, ι c ∈ T) (hz : z ∈ T) :
    scaledPolynomialRing O ι z ≤ T := by
  rintro _ ⟨P, rfl⟩
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ => simpa only [map_add] using T.add_mem hP hQ
  | monomial n c =>
    change (monomial n c).eval₂ (ι.comp O.subtype) z ∈ T
    rw [eval₂_monomial]
    exact T.mul_mem (hO c c.property) (T.pow_mem hz n)

/-- Concrete containment of Z_p[p^s t] in an actual subring of Q_p(t). -/
theorem padicScaledPolynomialRing_le (p : ℕ) [Fact p.Prime] (s : ℕ)
    (T : Subring (RatFunc ℚ_[p]))
    (hO : ∀ c ∈ PadicInt.subring p, RatFunc.C c ∈ T)
    (ht : RatFunc.C (p : ℚ_[p]) ^ s * RatFunc.X ∈ T) :
    padicScaledPolynomialRing p s ≤ T :=
  scaledPolynomialRing_le (PadicInt.subring p) RatFunc.C _ T hO ht

/-- The stage identities in the literal scaled ring imply an actual conductor
ideal inclusion. Its exponents and selected word may depend on requested precision. -/
theorem padic_pair_conductor_power_of_word_transfers
    (p : ℕ) [Fact p.Prime] (s R : ℕ) (α β : ℚ_[p])
    (hα : α ∈ PadicInt.subring p) (hβ : β ∈ PadicInt.subring p)
    (T B : Subring (RatFunc ℚ_[p]))
    (hO : ∀ c ∈ PadicInt.subring p, RatFunc.C c ∈ T)
    (ht : RatFunc.C (p : ℚ_[p]) ^ s * RatFunc.X ∈ T)
    (hinv : (RatFunc.C (p : ℚ_[p]))⁻¹ ∈ B)
    (hclear : ∀ b ∈ B, ∃ n : ℕ, RatFunc.C (p : ℚ_[p]) ^ n * b ∈ T)
    (hwords : ∀ k : ℕ, ∃ (i e : ℕ) (w : RatFunc ℚ_[p]),
      k ≤ i ∧ e ≤ R ∧ w ∈ T ∧
      ∃ u v : padicScaledPolynomialRing p s,
        (RatFunc.C (p : ℚ_[p]) ^ (2 * s) *
          ((RatFunc.X - RatFunc.C α) * (RatFunc.X - RatFunc.C β))) ^ e =
        RatFunc.C (p : ℚ_[p]) ^ i * ((u : RatFunc ℚ_[p]) + (v : RatFunc ℚ_[p]) * w)) :
    ∀ b ∈ B, ((RatFunc.X - RatFunc.C α) * (RatFunc.X - RatFunc.C β)) ^ R * b ∈ T := by
  let A := padicScaledPolynomialRing p s
  let π : A := ⟨RatFunc.C (p : ℚ_[p]), scalar_mem_scaledPolynomialRing
    (PadicInt.subring p) RatFunc.C _ (by simp)⟩
  let g : A := ⟨RatFunc.C (p : ℚ_[p]) ^ (2 * s) *
      ((RatFunc.X - RatFunc.C α) * (RatFunc.X - RatFunc.C β)),
    scaled_pair_mem_scaledPolynomialRing (PadicInt.subring p) RatFunc.C (p : ℚ_[p])
      α β (by simp) hα hβ RatFunc.X s⟩
  have hπ : (π : RatFunc ℚ_[p]) ≠ 0 := by
    change RatFunc.C (p : ℚ_[p]) ≠ 0
    exact (_root_.map_ne_zero RatFunc.C).mpr
      (Nat.cast_ne_zero.mpr (show p.Prime from Fact.out).ne_zero)
  exact conductor_power_of_word_transfers A T B
    (padicScaledPolynomialRing_le p s T hO ht) π g
    ((RatFunc.X - RatFunc.C α) * (RatFunc.X - RatFunc.C β)) s R hπ hinv rfl hclear hwords


/-- An extracted sequence with stages tending to infinity supplies every
requested precision. The words here are the literal polynomial quotients. -/
theorem padic_pair_conductor_power_of_eventual_word_transfers
    (p : ℕ) [Fact p.Prime] (s R : ℕ) (α β : ℚ_[p])
    (hα : α ∈ PadicInt.subring p) (hβ : β ∈ PadicInt.subring p)
    (T B : Subring (RatFunc ℚ_[p]))
    (hO : ∀ c ∈ PadicInt.subring p, RatFunc.C c ∈ T)
    (ht : RatFunc.C (p : ℚ_[p]) ^ s * RatFunc.X ∈ T)
    (hinv : (RatFunc.C (p : ℚ_[p]))⁻¹ ∈ B)
    (hclear : ∀ b ∈ B, ∃ n : ℕ, RatFunc.C (p : ℚ_[p]) ^ n * b ∈ T)
    (stage e : ℕ → ℕ) (F H : ℕ → ℚ_[p][X])
    (hstage : Tendsto stage atTop atTop)
    (hwords : ∀ᶠ n in atTop, e n ≤ R ∧
      ((F n : RatFunc ℚ_[p]) ^ e n / (H n : RatFunc ℚ_[p])) ∈ T ∧
      ∃ u v : padicScaledPolynomialRing p s,
        (RatFunc.C (p : ℚ_[p]) ^ (2 * s) *
          ((RatFunc.X - RatFunc.C α) * (RatFunc.X - RatFunc.C β))) ^ e n =
        RatFunc.C (p : ℚ_[p]) ^ stage n * ((u : RatFunc ℚ_[p]) +
          (v : RatFunc ℚ_[p]) * ((F n : RatFunc ℚ_[p]) ^ e n / (H n : RatFunc ℚ_[p])))) :
    ∀ b ∈ B, ((RatFunc.X - RatFunc.C α) * (RatFunc.X - RatFunc.C β)) ^ R * b ∈ T := by
  apply padic_pair_conductor_power_of_word_transfers p s R α β hα hβ T B hO ht hinv hclear
  intro k
  have hlarge : ∀ᶠ n in atTop, k ≤ stage n := hstage.eventually (eventually_ge_atTop k)
  obtain ⟨n, hn, he, hw, huv⟩ := (hlarge.and hwords).exists
  exact ⟨stage n, e n, _, hn, he, hw, huv⟩

end UnconditionalCounterexample.LocalAlgebra
