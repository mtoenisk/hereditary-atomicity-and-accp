import HereditaryAtomicity.DVRBase.SourceLaurent

/-!
# The finite Laurent model of actual source block data

The model parameters retain the literal source orders and thresholds.
The finite generator ring over the original coefficient fraction field lies
in the actual generator-defined model ring; source membership and formal
membership are separate statements.
-/

noncomputable section
namespace HereditaryAtomicity.DVRBase
open scoped BigOperators NNReal
variable {K : Type*} [Field K] {R : Subring K}
namespace SourceBlockData

variable (D : SourceBlockData R)

/-- The finite model parameters are exactly the source numerical data. -/
def modelParameters (n : ℕ) : ModelParameters n where
  kappa := D.exponent
  kappa_pos := D.exponent_pos
  weights := fun i => D.weight i.val
  weights_pos := fun i => D.ratio_order_pos i.val
  thresholds := D.threshold
  threshold_zero := D.threshold_zero
  threshold_large := fun _ hk _ => D.threshold_ge_two_exponent hk
  remaining_pos := by
    intro k hk
    rw [← D.endpointOrder_eq_remainingValue n k hk]
    exact lt_of_lt_of_le zero_lt_one (D.endpoint_order_ge_one k)

/-- The original coefficient uniformizer remains normalized in its actual fraction field. -/
theorem coefficientUniformizer_order (O : Subring K) (π : O)
    (hπ : (π : K) = (D.uniformizer : K)) :
    realValuationOrder (coefficientFractionValuation O D.valuation)
      (algebraMap O (FractionRing O) π) = 1 := by
  change realValuationOrder D.valuation
    (coefficientFractionEmbedding O (algebraMap O (FractionRing O) π)) = 1
  rw [coefficientFractionEmbedding_algebraMap, hπ]
  exact D.normalized

theorem coefficientUniformizer_ne_zero (O : Subring K) (π : O)
    (hπ : (π : K) = (D.uniformizer : K)) :
    algebraMap O (FractionRing O) π ≠ 0 := by
  intro hz
  have h := congrArg (coefficientFractionEmbedding O) hz
  rw [coefficientFractionEmbedding_algebraMap, map_zero, hπ] at h
  exact D.uniformizer_ne_zero (Subtype.ext h)

/-- For a nonzero formal monomial, its model order is exactly the source
valuation of its evaluation, with no independence assumption on the ratios. -/
theorem termOrder_eq_evaluation_single (O : Subring K) {n : ℕ}
    (β : Fin n → ℤ) (c : FractionRing O) (hc : c ≠ 0) :
    termOrder (coefficientFractionValuation O D.valuation) (D.modelParameters n).weights β c =
      realValuationOrder D.valuation (D.evaluation O n (AddMonoidAlgebra.single β c)) := by
  have hcK : coefficientFractionEmbedding O c ≠ 0 :=
    by simpa using (coefficientFractionEmbedding O).injective.ne hc
  have hy : ∀ i : Fin n, (D.ratio i.val : K) ≠ 0 :=
    fun i => Subtype.coe_ne_coe.mpr (D.ratio_ne_zero i.val)
  rw [evaluation, laurentEvaluation_single,
    realValuationOrder_mul D.valuation hcK (Finset.prod_ne_zero_iff.mpr
      (fun i _ => zpow_ne_zero _ (hy i)))]
  rw [realValuationOrder_prod]
  · simp only [realValuationOrder_zpow]
    rfl
  · intro i _
    exact zpow_ne_zero _ (hy i)

/-- Every first-dead generator is one of the actual high model generators. -/
theorem firstDead_formal_mem_modelRing (O : Subring K) (π : O)
    (hπ : (π : K) = (D.uniformizer : K)) {n : ℕ}
    (h : D.FirstDead) (hn : h.length ≤ n) :
    h.formal O π hn ∈ modelRing (coefficientFractionValuation O D.valuation)
      (algebraMap O (FractionRing O) π) (D.modelParameters n) := by
  let c := (algebraMap O (FractionRing O) π) ^ h.coefficientExponent /
    (algebraMap O (FractionRing O) π) ^ D.exponent
  have hc : c ≠ 0 := div_ne_zero (pow_ne_zero _ (D.coefficientUniformizer_ne_zero O π hπ))
    (pow_ne_zero _ (D.coefficientUniformizer_ne_zero O π hπ))
  rw [h.formal_eq_single]
  apply modelRing_high _ _ _ h.length h.length_pos hn _ _ hc
  · intro i hi
    rw [h.formalExponent_apply]
    simp [not_lt.mpr hi]
  · change D.threshold h.length ≤ termOrder _ _ _ c
    rw [D.termOrder_eq_evaluation_single O _ c hc]
    rw [← h.formal_eq_single O π hn, h.evaluation_formal O π hπ hn]
    exact h.threshold_le_value_order

/-- The actual finite source-generator ring is contained in the actual finite
model ring, over the original coefficient fraction field. -/
theorem formalRing_le_modelRing (O : Subring K) (π : O)
    (hπ : (π : K) = (D.uniformizer : K))
    (hO : ∀ a : O, D.valuation (a : K) ≤ 1) (n : ℕ) :
    D.formalRing O π n ≤ modelRing (coefficientFractionValuation O D.valuation)
      (algebraMap O (FractionRing O) π) (D.modelParameters n) := by
  apply Subring.closure_le.mpr
  intro f hf
  cases hf with
  | coefficient a =>
      apply modelRing_constant
      change D.valuation (coefficientFractionEmbedding O (algebraMap O (FractionRing O) a)) ≤ 1
      rw [coefficientFractionEmbedding_algebraMap]
      exact hO a
  | coordinate i => exact modelRing_variable _ _ _ i
  | endpoint j _hj =>
      exact modelJunk_le_modelRing _ _ _ (endpointMonomial_mem_modelJunk _ _ _ j)
  | firstDead h hn => exact D.firstDead_formal_mem_modelRing O π hπ h hn

end SourceBlockData
end HereditaryAtomicity.DVRBase
