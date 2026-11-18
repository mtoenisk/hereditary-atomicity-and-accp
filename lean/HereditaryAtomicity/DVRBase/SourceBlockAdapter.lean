import HereditaryAtomicity.DVRBase.BlockConstruction
import HereditaryAtomicity.DVRBase.SourceConstruction

/-! The recursive block output in its original literal source ring. -/

noncomputable section
open scoped NNReal
namespace HereditaryAtomicity.DVRBase.BlockInput

variable {K k L : Type*} [Field K] [Field k] [Field L] [Algebra k L]
  {R : Subring K} {π : R} {t : ℕ → R}
  (I : BlockInput R k L π t) (loss : ℕ → BlockState k L → ℝ)
  (w : Valuation K ℝ≥0) (hw : ∀ r : R, I.valuation (I.embedding r) = w (r : K))

/-- The recursive block output retains its literal source ring when the
ambient valuation is the extension of the original source valuation. -/
def toSourceBlockData : SourceBlockData R where
  uniformizer := π
  uniformizer_ne_zero := by
    intro h
    have hn := I.uniformizer_order
    simp [h] at hn
  exponent := I.chain.exponent
  exponent_pos := I.chain.exponent_pos
  ratio := I.sourceY loss
  endpoint := I.sourceZ loss
  endpoint_ne_zero := I.sourceZ_ne_zero loss
  top := I.sourceZ_zero loss
  step := I.sourceZ_step loss
  valuation := w
  normalized := by
    simpa only [realValuationOrder, hw] using I.uniformizer_order
  ratio_order_pos n := by
    simpa only [blockOrder, realValuationOrder, hw] using I.blockOrder_pos loss n
  endpoint_order_ge_one n := by
    simpa only [endpointOrder, realValuationOrder, hw] using I.one_le_endpointOrder loss n
  returnExponent := I.returnExponent loss
  returnExponent_pos := I.returnExponent_pos loss
  power_return := I.sourceY_power_return loss

@[simp] theorem toSourceBlockData_ratio (n : ℕ) :
    (I.toSourceBlockData loss w hw).ratio n = I.sourceY loss n := rfl

@[simp] theorem toSourceBlockData_endpoint (n : ℕ) :
    (I.toSourceBlockData loss w hw).endpoint n = I.sourceZ loss n := rfl

theorem toSourceBlockData_weight (n : ℕ) :
    (I.toSourceBlockData loss w hw).weight n = I.blockOrder loss n := by
  simp only [SourceBlockData.weight, toSourceBlockData, blockOrder, realValuationOrder, hw]

theorem toSourceBlockData_threshold (n : ℕ) :
    (I.toSourceBlockData loss w hw).threshold n = I.threshold loss n := by
  rw [I.threshold_eq_sum]
  change 2 * (I.chain.exponent : ℝ) * ∑ i : Fin n, (I.returnExponent loss i.val : ℝ) = _
  rw [Fin.sum_univ_eq_sum_range (fun j => (I.returnExponent loss j : ℝ)) n]

end HereditaryAtomicity.DVRBase.BlockInput
