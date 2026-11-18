import HereditaryAtomicity.DVRBase.GeometricApproximation
import HereditaryAtomicity.DVRBase.GaussBounds

/-!
# Matching least collected terms after a finite approximation

The error is strictly smaller in Gauss value than the larger of the two
polynomials. Their coefficients outside the permitted support class must
then attain the same least order, including when either polynomial was
initially allowed to vanish.
-/

noncomputable section
namespace HereditaryAtomicity.DVRBase
open scoped BigOperators NNReal
variable {K : Type*} [Field K] {n : ℕ}

private theorem ne_zero_of_coeff_ne_zero {f : Laurent K n} {β : Fin n → ℤ}
    (hβ : f.coeff β ≠ 0) : f ≠ 0 := by
  intro h
  exact hβ (by simp [h])

/-- A lower bound attained at an actual nonzero coefficient equals the
finite Gauss order; the zero-polynomial convention is never used. -/
theorem laurentOrder_eq_of_bounds_and_attainment
    (v : Valuation K ℝ≥0) (u : Fin n → ℝ) (f : Laurent K n) (ν : ℝ)
    (hbound : ∀ β, f.coeff β ≠ 0 → ν ≤ termOrder v u β (f.coeff β))
    (β : Fin n → ℤ) (hβ : f.coeff β ≠ 0)
    (hattain : termOrder v u β (f.coeff β) = ν) : laurentOrder v u f = ν := by
  apply le_antisymm ((laurentOrder_le_termOrder v u f hβ).trans_eq hattain)
  obtain ⟨γ, hγ, heq⟩ := exists_termOrder_eq_laurentOrder v u f
    (ne_zero_of_coeff_ne_zero hβ)
  rw [← heq]
  exact hbound γ hγ

/-- The low terms of two polynomials outside a support class match after
subtracting a permitted term and a strictly smaller residual. -/
theorem same_least_terms_of_small_residual
    (v : Valuation K ℝ≥0) (u : Fin n → ℝ) (M : MonomialClass n)
    (f g r : Laurent K n) (hf : f ≠ 0) (hr : r ∈ M.supported v)
    (hfM : ∀ β, f.coeff β ≠ 0 → ¬ M.contains β (realValuationOrder v (f.coeff β)))
    (hgM : ∀ β, g.coeff β ≠ 0 → ¬ M.contains β (realValuationOrder v (g.coeff β)))
    (herr : laurentGaussValue v u (f - g - r) <
      max (laurentGaussValue v u f) (laurentGaussValue v u g)) :
    g ≠ 0 ∧ laurentOrder v u f = laurentOrder v u g ∧
      ∀ β, (f.coeff β ≠ 0 ∧ termOrder v u β (f.coeff β) = laurentOrder v u f) ↔
        (g.coeff β ≠ 0 ∧ termOrder v u β (g.coeff β) = laurentOrder v u f) := by
  let B := max (laurentGaussValue v u f) (laurentGaussValue v u g)
  let ν : ℝ := -Real.log (B : ℝ)
  have hfv : 0 < laurentGaussValue v u f := gaussValue_pos v _ hf
  have hB : 0 < B := lt_of_lt_of_le hfv (le_max_left _ _)
  have hexp : Real.exp (-ν) = (B : ℝ) := by
    dsimp [ν]
    rw [neg_neg, Real.exp_log (by exact_mod_cast hB)]
  have hfb : ∀ β, f.coeff β ≠ 0 → ν ≤ termOrder v u β (f.coeff β) := by
    apply (laurentGaussValue_le_exp_iff v u f ν).mp
    rw [hexp]
    exact_mod_cast le_max_left (laurentGaussValue v u f) (laurentGaussValue v u g)
  have hgb : ∀ β, g.coeff β ≠ 0 → ν ≤ termOrder v u β (g.coeff β) := by
    apply (laurentGaussValue_le_exp_iff v u g ν).mp
    rw [hexp]
    exact_mod_cast le_max_right (laurentGaussValue v u f) (laurentGaussValue v u g)
  have he : f - g - r ∈ (higherOrder u ν).supported v := by
    apply (mem_higherOrder_supported_iff v u _ ν).mpr
    rw [hexp]
    exact_mod_cast herr
  have hdiff : f - g ∈ (M.union (higherOrder u ν)).supported v := by
    rw [MonomialClass.supported_union]
    exact AddSubgroup.mem_sup.mpr ⟨r, hr, f - g - r, he, by ring⟩
  have hiff := threshold_support_iff_of_difference_supported v u M hdiff hfM hgM hfb hgb
  have hattain : ∃ β, (f.coeff β ≠ 0 ∧ termOrder v u β (f.coeff β) = ν) ∧
      (g.coeff β ≠ 0 ∧ termOrder v u β (g.coeff β) = ν) := by
    rcases le_total (laurentGaussValue v u g) (laurentGaussValue v u f) with hgf | hfg
    · obtain ⟨β, hβ, heq⟩ := exists_termOrder_eq_laurentOrder v u f hf
      have hord : laurentOrder v u f = ν := by
        dsimp [laurentOrder, ν, B]
        rw [max_eq_left hgf]
      have hb : f.coeff β ≠ 0 ∧ termOrder v u β (f.coeff β) = ν := ⟨hβ, heq.trans hord⟩
      exact ⟨β, hb, (hiff β).mp hb⟩
    · have hg : g ≠ 0 := by
        intro hg
        have hz : laurentGaussValue v u g = 0 := by simp [hg, laurentGaussValue]
        rw [hz] at hfg
        exact (not_le_of_gt hfv) hfg
      obtain ⟨β, hβ, heq⟩ := exists_termOrder_eq_laurentOrder v u g hg
      have hord : laurentOrder v u g = ν := by
        dsimp [laurentOrder, ν, B]
        rw [max_eq_right hfg]
      have hb : g.coeff β ≠ 0 ∧ termOrder v u β (g.coeff β) = ν := ⟨hβ, heq.trans hord⟩
      exact ⟨β, (hiff β).mpr hb, hb⟩
  obtain ⟨β, hβf, hβg⟩ := hattain
  have hfo := laurentOrder_eq_of_bounds_and_attainment v u f ν hfb β hβf.1 hβf.2
  have hgo := laurentOrder_eq_of_bounds_and_attainment v u g ν hgb β hβg.1 hβg.2
  refine ⟨ne_zero_of_coeff_ne_zero hβg.1, hfo.trans hgo.symm, ?_⟩
  intro γ
  simpa only [hfo] using hiff γ

/-- Apply the finite geometric approximation to the actual Laurent Gauss
valuation. The auxiliary ring is retained explicitly. -/
theorem geometric_same_least_terms
    (v : Valuation K ℝ≥0) (u : Fin n → ℝ) (M : MonomialClass n)
    (R U : Subring (Laurent K n)) (hR : R.toAddSubgroup = M.supported v)
    (ψ ρ Y e d j b : Laurent K n) (hψ : ψ ≠ 0)
    (hρ : ρ ∈ R) (hY : Y ∈ R) (he : e ∈ R)
    (hYU : ∀ x ∈ U, Y * x ∈ R) (hjU : j ∈ U)
    (hdb : d = j + b)
    (hj : laurentGaussValue v u j ≤ laurentGaussValue v u d)
    (hd : laurentGaussValue v u d < 1) (hev : laurentGaussValue v u e < 1)
    (heq : (ψ + ρ) * (1 - d) = Y * (1 + e))
    (hψM : ∀ β, ψ.coeff β ≠ 0 → ¬ M.contains β (realValuationOrder v (ψ.coeff β)))
    (hbM : ∀ β, (Y * b).coeff β ≠ 0 →
      ¬ M.contains β (realValuationOrder v ((Y * b).coeff β))) :
    Y * b ≠ 0 ∧ laurentOrder v u ψ = laurentOrder v u (Y * b) ∧
      ∀ β, (ψ.coeff β ≠ 0 ∧ termOrder v u β (ψ.coeff β) = laurentOrder v u ψ) ↔
        ((Y * b).coeff β ≠ 0 ∧
          termOrder v u β ((Y * b).coeff β) = laurentOrder v u ψ) := by
  let B := max (laurentGaussValue v u ψ) (laurentGaussValue v u (Y * b))
  have hB : 0 < B := lt_of_lt_of_le (gaussValue_pos v _ hψ) (le_max_left _ _)
  obtain ⟨r, hr, herr⟩ := exists_geometric_ring_approximation (laurentGaussValuation v u)
    R U ψ ρ Y e d j b hρ hY he hYU hjU hdb hj hd hev heq B hB (le_max_right _ _)
  apply same_least_terms_of_small_residual v u M ψ (Y * b) r hψ _ hψM hbM herr
  rw [← hR]
  exact hr

end HereditaryAtomicity.DVRBase
