import UnconditionalCounterexample.LocalAlgebra.TransverseIdeal

/-!
# Transfer by a single scheduled word

Proposition 3.1(4) takes place in the module spanned by 1 and the word over
the scaled polynomial ring. The first lemma gives both coefficients. The
second uses that identity inside the conductor proof of Lemma 6.1.
-/

namespace UnconditionalCounterexample.LocalAlgebra

variable {K : Type*} [Field K]

/-- The two coefficient estimates for a normalized numerator and a word
denominator imply the two-term identity of Proposition 3.1(4). -/
theorem exists_word_transfer_coefficients (A : Subring K) (π f g : A)
    (F H w scale C₀ : K) (i a : ℕ) (ha : 0 < a) (hC : C₀ ≠ 0) (hH : H ≠ 0)
    (hscale : scale ∈ A) (hinv : C₀⁻¹ ∈ A) (hf : (f : K) = scale * F / C₀)
    (hw : w = F ^ a / H) (hcong : π ^ i ∣ f - g)
    (hden : ∃ V : A, H / C₀ = (π : K) ^ i * (V : K)) :
    ∃ u v : A, (g : K) ^ a = (π : K) ^ i * ((u : K) + (v : K) * w) := by
  obtain ⟨V, hV⟩ := hden
  obtain ⟨U, hU⟩ := hcong.trans (sub_dvd_pow_sub_pow f g a)
  have hdiff := congrArg (fun z : A => (z : K)) hU
  simp only [AddSubgroupClass.coe_sub, Subring.coe_pow, Subring.coe_mul] at hdiff
  obtain ⟨b, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt ha)
  let v : A := ⟨scale ^ (b + 1) * (C₀⁻¹) ^ b * V,
    A.mul_mem (A.mul_mem (A.pow_mem hscale _) (A.pow_mem hinv _)) V.property⟩
  have hscaled : (π : K) ^ i * ((v : K) * w) = (f : K) ^ (b + 1) := by
    change (π : K) ^ i * ((scale ^ (b + 1) * (C₀⁻¹) ^ b * (V : K)) * w) = _
    rw [show (π : K) ^ i * ((scale ^ (b + 1) * (C₀⁻¹) ^ b * (V : K)) * w) =
        scale ^ (b + 1) * (C₀⁻¹) ^ b * ((π : K) ^ i * (V : K)) * w by ring,
      ← hV, hf, hw]
    simp only [div_eq_mul_inv, mul_pow, pow_succ]
    field_simp
  refine ⟨-U, v, ?_⟩
  simp only [NegMemClass.coe_neg, mul_add, mul_neg, hscaled]
  simp only [pow_succ] at hdiff ⊢
  linear_combination -hdiff

/-- Transfer from one extracted stage to a fixed requested precision, even
when the stage and the exponent depend on that precision. -/
theorem inverse_power_of_word_transfer (A T : Subring K) (hAT : A ≤ T)
    (π g : A) (w : K) (i k e R : ℕ) (hki : k ≤ i) (heR : e ≤ R)
    (hπ : (π : K) ≠ 0) (hw : w ∈ T)
    (htransfer : ∃ u v : A, (g : K) ^ e = (π : K) ^ i * ((u : K) + (v : K) * w)) :
    (g : K) ^ R / (π : K) ^ k ∈ T := by
  obtain ⟨u, v, huv⟩ := htransfer
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hki
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le heR
  rw [pow_add, huv, pow_add, mul_assoc, mul_assoc, mul_div_cancel_left₀ _ (pow_ne_zero _ hπ)]
  exact T.mul_mem (T.pow_mem (hAT π.property) _)
    (T.mul_mem (T.add_mem (hAT u.property) (T.mul_mem (hAT v.property) hw))
      (T.pow_mem (hAT g.property) _))

/-- Lemma 6.1 from the stage estimates on an extracted sequence. For each
precision the stage and the exponent may vary. Multiplying by an inverse
scalar in the ambient algebra removes the normalization of the quadratic. -/
theorem conductor_power_of_word_transfers (A T B : Subring K) (hAT : A ≤ T)
    (π g : A) (L : K) (s R : ℕ) (hπ : (π : K) ≠ 0)
    (hinv : (π : K)⁻¹ ∈ B) (hg : (g : K) = (π : K) ^ (2 * s) * L)
    (hclear : ∀ b ∈ B, ∃ n : ℕ, (π : K) ^ n * b ∈ T)
    (hwords : ∀ k : ℕ, ∃ (i e : ℕ) (w : K), k ≤ i ∧ e ≤ R ∧ w ∈ T ∧
      ∃ u v : A, (g : K) ^ e = (π : K) ^ i * ((u : K) + (v : K) * w)) :
    ∀ b ∈ B, L ^ R * b ∈ T := by
  have hpower (k : ℕ) : (g : K) ^ R / (π : K) ^ k ∈ T := by
    obtain ⟨i, e, w, hi, he, hw, huv⟩ := hwords k
    exact inverse_power_of_word_transfer A T hAT π g w i k e R hi he hπ hw huv
  intro b hb
  have h := conductor_of_inverse_powers T B π ((g : K) ^ R) hπ hpower hclear
    (((π : K)⁻¹ ^ (2 * s)) ^ R * b) (B.mul_mem (B.pow_mem (B.pow_mem hinv _) _) hb)
  rw [hg, mul_pow, inv_pow, inv_pow] at h
  convert h using 1
  field_simp

end UnconditionalCounterexample.LocalAlgebra
