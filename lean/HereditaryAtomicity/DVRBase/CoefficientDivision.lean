import HereditaryAtomicity.DVRBase.CoefficientShrinking

/-!
# Division closure for actual DVR coefficient rings

A normalized valuation bounded on an actual DVR gives precisely the division
closure used in coefficient transfer. This makes division closure automatic when the smaller coefficient
ring is itself a DVR with the same uniformizer.
-/

noncomputable section
namespace HereditaryAtomicity.DVRBase
open scoped NNReal
variable {K : Type*} [Field K]

/-- Every normalized bounded valuation on a DVR gives division closure for its actual
uniformizer, including division by every smaller nonnegative power. -/
theorem uniformizerDivisionClosed_of_dvr
    (B : Subring K) [IsDiscreteValuationRing B] (π : B) (hπ : Irreducible π)
    (v : Valuation K ℝ≥0) (hB : ∀ c : B, v (c : K) ≤ 1)
    (hnorm : realValuationOrder v (π : K) = 1) :
    UniformizerDivisionClosed B π v := by
  intro c hc e he
  obtain ⟨n, u, hfactor, _, hord, _⟩ :=
    exists_normalized_dvr_coefficient_power B π hπ v hB hnorm c hc
  have hen : e ≤ n := by rw [hord] at he; exact_mod_cast he
  have hp : (π : K) ≠ 0 := Subtype.coe_ne_coe.mpr hπ.ne_zero
  have heq : (c : K) / (π : K) ^ e = ((u : B) : K) * (π : K) ^ (n - e) := by
    rw [hfactor, pow_sub₀ _ hp hen, div_eq_mul_inv, mul_assoc]
  rw [heq]
  exact B.mul_mem (u : B).property (B.pow_mem π.property _)

end HereditaryAtomicity.DVRBase
