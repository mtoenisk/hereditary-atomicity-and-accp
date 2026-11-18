import HereditaryAtomicity.DVRBase.Laurent

/-!
# Matching low terms modulo a monomial support class

Matching collected coefficients outside the model ring survives subtraction of a
strictly higher-order error. The comparison allows cancellation and zero coefficients.
-/

noncomputable section
namespace HereditaryAtomicity.DVRBase

open scoped BigOperators NNReal

variable {K : Type*} [Field K] {n : ℕ}

/-- Monomials of weighted order strictly above a chosen real threshold. -/
def higherOrder (u : Fin n → ℝ) (ν : ℝ) : MonomialClass n where
  contains β e := ν < e + ∑ i, (β i : ℝ) * u i
  upward := by
    intro β a b hab ha
    linarith

/-- A least-order term outside a support class must be matched at the same
exponent and order when the difference belongs to that class modulo higher
order. This does not assume that the coefficients themselves are equal. -/
theorem matching_term_of_difference_supported
    (v : Valuation K ℝ≥0) (u : Fin n → ℝ) (M : MonomialClass n)
    {ν : ℝ} {f g : Laurent K n} {β : Fin n → ℤ}
    (hdiff : f - g ∈ (M.union (higherOrder u ν)).supported v)
    (hf0 : f.coeff β ≠ 0)
    (hfν : termOrder v u β (f.coeff β) = ν)
    (hfM : ¬ M.contains β (realValuationOrder v (f.coeff β)))
    (hgν : g.coeff β ≠ 0 → ν ≤ termOrder v u β (g.coeff β)) :
    g.coeff β ≠ 0 ∧ termOrder v u β (g.coeff β) = ν := by
  have hbad (hδ : (f - g).coeff β ≠ 0)
      (horder : realValuationOrder v ((f - g).coeff β) =
        realValuationOrder v (f.coeff β)) : False := by
    have h := (MonomialClass.mem_supported v _).mp hdiff β hδ
    rcases h with h | h
    · exact hfM (horder ▸ h)
    · change ν < realValuationOrder v ((f - g).coeff β) +
        ∑ i, (β i : ℝ) * u i at h
      rw [horder] at h
      change ν < termOrder v u β (f.coeff β) at h
      exact (lt_irrefl ν) (hfν ▸ h)
  have hg0 : g.coeff β ≠ 0 := by
    intro hzero
    apply hbad
    · simpa [hzero] using hf0
    · simp [hzero]
  refine ⟨hg0, ?_⟩
  by_contra hne
  have hlt : ν < termOrder v u β (g.coeff β) :=
    lt_of_le_of_ne (hgν hg0) (Ne.symm hne)
  have hord : realValuationOrder v (f.coeff β) <
      realValuationOrder v (g.coeff β) := by
    unfold termOrder at hfν hlt
    linarith
  obtain ⟨hδ, hδorder⟩ := realValuationOrder_add_eq_min v hf0
    (neg_ne_zero.mpr hg0) (by simpa using (ne_of_lt hord))
  apply hbad
  · simpa only [sub_eq_add_neg, AddMonoidAlgebra.coeff_add,
      AddMonoidAlgebra.coeff_neg, Finsupp.add_apply, Finsupp.neg_apply] using hδ
  · simpa only [sub_eq_add_neg, AddMonoidAlgebra.coeff_add,
      AddMonoidAlgebra.coeff_neg, Finsupp.add_apply, Finsupp.neg_apply,
      realValuationOrder_neg, min_eq_left hord.le] using hδorder

/-- At the threshold, supports agree outside the allowed monomial class.
Both directions are needed when either of the two polynomials attains the
least order in the coefficient-matching argument. -/
theorem threshold_support_iff_of_difference_supported
    (v : Valuation K ℝ≥0) (u : Fin n → ℝ) (M : MonomialClass n)
    {ν : ℝ} {f g : Laurent K n}
    (hdiff : f - g ∈ (M.union (higherOrder u ν)).supported v)
    (hfM : ∀ β, f.coeff β ≠ 0 → ¬ M.contains β (realValuationOrder v (f.coeff β)))
    (hgM : ∀ β, g.coeff β ≠ 0 → ¬ M.contains β (realValuationOrder v (g.coeff β)))
    (hfν : ∀ β, f.coeff β ≠ 0 → ν ≤ termOrder v u β (f.coeff β))
    (hgν : ∀ β, g.coeff β ≠ 0 → ν ≤ termOrder v u β (g.coeff β))
    (β : Fin n → ℤ) :
    (f.coeff β ≠ 0 ∧ termOrder v u β (f.coeff β) = ν) ↔
      (g.coeff β ≠ 0 ∧ termOrder v u β (g.coeff β) = ν) := by
  constructor
  · rintro ⟨hf0, heq⟩
    exact matching_term_of_difference_supported v u M hdiff hf0 heq (hfM β hf0) (hgν β)
  · rintro ⟨hg0, heq⟩
    have hreverse : g - f ∈ (M.union (higherOrder u ν)).supported v := by
      simpa only [neg_sub] using ((M.union (higherOrder u ν)).supported v).neg_mem hdiff
    exact matching_term_of_difference_supported v u M hreverse hg0 heq (hgM β hg0) (hfν β)

end HereditaryAtomicity.DVRBase
