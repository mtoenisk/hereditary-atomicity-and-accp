import HereditaryAtomicity.DVRBase.SourceProductTerms
import HereditaryAtomicity.DVRBase.KernelNumerics

/-!
# Numerical kernel estimates for literal source-product terms

First-dead factors are indexed by their occurrences in a list, preserving
multiplicity. The formulas use the actual source coefficient, natural
coordinate/endpoint counts, and exact first-dead levels. No replacement
product-count or coefficient-order hypothesis stands in for the source data.
-/

noncomputable section
namespace HereditaryAtomicity.DVRBase
open scoped BigOperators NNReal

/-- Prefix sums agree under extension to a larger finite ambient stage. -/
theorem prefixSum_stage_eq {m n : ℕ} (hmn : m ≤ n)
    (f : Fin m → ℝ) (g : Fin n → ℝ)
    (hfg : ∀ i, f i = g ⟨i.val, i.isLt.trans_le hmn⟩)
    (k : ℕ) (hk : k ≤ m) : prefixSum f k = prefixSum g k := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hkm : k < m := by omega
      rw [prefixSum_succ f hkm, prefixSum_succ g (hkm.trans_le hmn),
        ih (by omega), hfg ⟨k, hkm⟩]

theorem list_sum_map_eq_fin_sum {α A : Type*} [AddCommMonoid A]
    (l : List α) (f : α → A) :
    (l.map f).sum = ∑ i : Fin l.length, f (l.get i) := by
  simpa only [List.map_ofFn, List.sum_ofFn, Function.comp_def] using
    (congrArg (fun xs : List α => (xs.map f).sum) (List.ofFn_get l)).symm

namespace SourceBlockData
variable {K : Type*} [Field K] {R : Subring K} {D : SourceBlockData R} {n : ℕ}
namespace FirstDead

/-- Extension of the literal first-dead powers by zero at later coordinates. -/
def stagePowers (h : D.FirstDead) (n : ℕ) : Fin n → ℕ :=
  fun i => if hi : i.val < h.length then h.powers ⟨i.val, hi⟩ else 0

theorem stage_partialValue (h : D.FirstDead) (hn : h.length ≤ n)
    (k : ℕ) (hk : k ≤ h.length) :
    partialValue (fun i : Fin n => D.weight i.val) h.coefficientExponent
      (fun i => (h.stagePowers n i : ℤ)) k =
    partialValue (fun i : Fin h.length => D.weight i.val) h.coefficientExponent
      (fun i => (h.powers i : ℤ)) k := by
  unfold partialValue
  congr 1
  symm
  apply prefixSum_stage_eq hn _ _ _ k hk
  intro i
  simp [stagePowers, i.isLt]

theorem stage_remainingValue (h : D.FirstDead) (hn : h.length ≤ n)
    (k : ℕ) (hk : k ≤ h.length) :
    remainingValue (fun i : Fin n => D.weight i.val) D.exponent k =
    remainingValue (fun i : Fin h.length => D.weight i.val) D.exponent k := by
  rw [← D.endpointOrder_eq_remainingValue n k (hk.trans hn),
    ← D.endpointOrder_eq_remainingValue h.length k hk]

/-- A first-dead source factor gives the numerical generator with its exact
original length, coefficient exponent, and powers, in every later stage. -/
def kernelGenerator (h : D.FirstDead) (hn : h.length ≤ n) :
    KernelGenerator (fun i : Fin n => D.weight i.val) D.exponent D.threshold where
  level := h.length
  level_pos := h.length_pos
  level_le := hn
  coefficientExponent := h.coefficientExponent
  powers := h.stagePowers n
  dead := by
    rw [h.stage_partialValue hn h.length le_rfl, h.stage_remainingValue hn h.length le_rfl]
    exact h.dead
  earlier := by
    intro k hk
    rw [h.stage_partialValue hn k hk.le, h.stage_remainingValue hn k hk.le]
    exact lt_of_not_ge (h.earlier k hk)

theorem formalExponent_eq_contribution (h : D.FirstDead) (hn : h.length ≤ n)
    (i : Fin n) : h.formalExponent hn i = ((h.kernelGenerator hn).contribution i : ℤ) := by
  rw [h.formalExponent_apply]
  by_cases hi : i.val < h.length
  · simp [kernelGenerator, KernelGenerator.contribution, stagePowers, hi]
  · simp [kernelGenerator, KernelGenerator.contribution, hi]

end FirstDead

namespace FormalProduct
variable {O : Subring K} (p : D.FormalProduct O n)

/-- Occurrences, rather than distinct source factors, index this finite family. -/
def kernelGenerators (j : Fin p.deadFactors.length) :
    KernelGenerator (fun i : Fin n => D.weight i.val) D.exponent D.threshold :=
  (p.deadFactors.get j).val.kernelGenerator (p.deadFactors.get j).property

/-- The source product's exact exponent equals the count-based kernel vector. -/
theorem formalExponent_eq_kernelProductExponent :
    p.formalExponent = kernelProductExponent p.variablePowers p.endpointPowers p.kernelGenerators := by
  funext i
  rw [p.formalExponent_apply]
  simp only [kernelProductExponent, kernelEndpointTail, kernelGeneratorCount, Nat.cast_sum]
  congr 1
  rw [list_sum_map_eq_fin_sum]
  apply Finset.sum_congr rfl
  intro j _
  exact FirstDead.formalExponent_eq_contribution _ _ i

/-- The coefficient identity for any normalized valuation on the original
coefficient fraction field, independent of later transport to a completion. -/
theorem formalCoefficient_order_eq_kernelProductCoefficient_of_valuation
    (π : O) (v : Valuation (FractionRing O) ℝ≥0) (hπ : π ≠ 0)
    (hvπ : realValuationOrder v (algebraMap O (FractionRing O) π) = 1)
    (hc : p.coefficient ≠ 0) :
    realValuationOrder v (p.formalCoefficient π) =
      kernelProductCoefficient (realValuationOrder v
        (algebraMap O (FractionRing O) p.coefficient)) p.endpointPowers p.kernelGenerators := by
  rw [p.formalCoefficient_order π v hπ hvπ hc, list_sum_map_eq_fin_sum]
  rfl

/-- Exact coefficient-count identity after a valuation-preserving embedding.
This equality rewrites the scalar order in any later levelValue expression. -/
theorem formalCoefficient_mapped_order_eq_kernelProductCoefficient
    {L : Type*} [Field L] (π : O) (v : Valuation (FractionRing O) ℝ≥0)
    (f : FractionRing O →+* L) (w : Valuation L ℝ≥0)
    (hval : ∀ c, w (f c) = v c) (hπ : π ≠ 0)
    (hvπ : realValuationOrder v (algebraMap O (FractionRing O) π) = 1)
    (hc : p.coefficient ≠ 0) :
    realValuationOrder w (f (p.formalCoefficient π)) =
      kernelProductCoefficient (realValuationOrder v
        (algebraMap O (FractionRing O) p.coefficient)) p.endpointPowers p.kernelGenerators := by
  have horder : realValuationOrder w (f (p.formalCoefficient π)) =
      realValuationOrder v (p.formalCoefficient π) := by
    simp only [realValuationOrder, hval]
  rw [horder, p.formalCoefficient_order_eq_kernelProductCoefficient_of_valuation π v hπ hvπ hc]

/-- The original coefficient order is exactly the coefficient count expression. -/
theorem formalCoefficient_order_eq_kernelProductCoefficient (π : O)
    (hπ : (π : K) = (D.uniformizer : K)) (hc : p.coefficient ≠ 0) :
    realValuationOrder (coefficientFractionValuation O D.valuation) (p.formalCoefficient π) =
      kernelProductCoefficient (realValuationOrder D.valuation (p.coefficient : K))
        p.endpointPowers p.kernelGenerators := by
  have hπO : π ≠ 0 := by
    intro hz
    apply D.uniformizer_ne_zero
    apply Subtype.ext
    simpa [hz] using hπ.symm
  have hvπ : realValuationOrder (coefficientFractionValuation O D.valuation)
      (algebraMap O (FractionRing O) π) = 1 := by
    change realValuationOrder D.valuation
      (coefficientFractionEmbedding O (algebraMap O (FractionRing O) π)) = 1
    rw [coefficientFractionEmbedding_algebraMap, hπ, D.normalized]
  rw [p.formalCoefficient_order π (coefficientFractionValuation O D.valuation) hπO hvπ hc]
  have hcoeff : realValuationOrder (coefficientFractionValuation O D.valuation)
      (algebraMap O (FractionRing O) p.coefficient) =
      realValuationOrder D.valuation (p.coefficient : K) := by
    change realValuationOrder D.valuation
      (coefficientFractionEmbedding O (algebraMap O (FractionRing O) p.coefficient)) = _
    rw [coefficientFractionEmbedding_algebraMap]
  rw [hcoeff, list_sum_map_eq_fin_sum]
  rfl

/-- The actual check cut keeps every first-dead factor occurrence and the failed cut. -/
def checkCut (i : Fin n) : ℕ := kernelCheckCut (i.val + 1) p.kernelGenerators

theorem checkCut_le (i : Fin n) : p.checkCut i ≤ n :=
  kernelCheckCut_le i.isLt p.kernelGenerators

theorem failedCut_le_checkCut (i : Fin n) : i.val + 1 ≤ p.checkCut i :=
  kernelCheckCut_ge _ _

/-- The full source-product estimate for an arbitrary normalized coefficient
valuation. The finite source orders and thresholds are exactly those of D. -/
theorem failed_window_estimate_of_valuation (π : O)
    (v : Valuation (FractionRing O) ℝ≥0) (hπ : π ≠ 0)
    (hvπ : realValuationOrder v (algebraMap O (FractionRing O) π) = 1)
    (hO : ∀ a : O, v (algebraMap O (FractionRing O) a) ≤ 1)
    (hc : p.coefficient ≠ 0) (i : Fin n) (degree : ℕ) (Ω : ℝ)
    (hfail : correctedDigit p.formalExponent i ∉ digitInterval degree)
    (hdegree : 3 * (D.exponent : ℝ) * (2 * D.threshold (i.val + 1) + Ω) ≤
      (degree : ℝ) * D.weight i.val) :
    D.threshold (p.checkCut i) + D.threshold (i.val + 1) + Ω ≤
      levelValue (fun j : Fin n => D.weight j.val) D.exponent
        (realValuationOrder v (p.formalCoefficient π)) p.formalExponent (p.checkCut i) := by
  rw [p.formalExponent_eq_kernelProductExponent] at hfail ⊢
  rw [p.formalCoefficient_order_eq_kernelProductCoefficient_of_valuation π v hπ hvπ hc]
  have hcoeff : algebraMap O (FractionRing O) p.coefficient ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective O (FractionRing O))).mpr hc
  exact kernelProduct_failed_window_estimate
    (fun j => (D.ratio_order_pos j.val).le)
    (by exact_mod_cast D.exponent_pos)
    (fun j => (D.weight_lt_exponent j.val).le)
    (fun k hk => by
      change 1 ≤ remainingValue (fun j : Fin n => D.weight j.val) D.exponent k
      rw [← D.endpointOrder_eq_remainingValue n k hk]
      exact D.endpoint_order_ge_one k)
    (fun k hk _ => D.threshold_ge_two_exponent hk)
    (realValuationOrder v (algebraMap O (FractionRing O) p.coefficient))
    ((realValuationOrder_nonneg_iff v hcoeff).mpr (hO p.coefficient))
    p.variablePowers p.endpointPowers p.kernelGenerators i degree Ω hfail hdegree

/-- The after-loss bound with any normalized valuation on the original
coefficient fraction field; all product data remain literal. -/
theorem after_loss_of_valuation (π : O)
    (v : Valuation (FractionRing O) ℝ≥0) (hπ : π ≠ 0)
    (hvπ : realValuationOrder v (algebraMap O (FractionRing O) π) = 1)
    (hO : ∀ a : O, v (algebraMap O (FractionRing O) a) ≤ 1)
    (hc : p.coefficient ≠ 0) (i : Fin n) (degree : ℕ) (Ω value : ℝ)
    (hfail : correctedDigit p.formalExponent i ∉ digitInterval degree)
    (hdegree : 3 * (D.exponent : ℝ) * (2 * D.threshold (i.val + 1) + Ω) ≤
      (degree : ℝ) * D.weight i.val)
    (hloss : levelValue (fun j : Fin n => D.weight j.val) D.exponent
        (realValuationOrder v (p.formalCoefficient π)) p.formalExponent (p.checkCut i) - Ω ≤ value) :
    D.threshold (p.checkCut i) + D.endpointOrder (p.checkCut i) + D.endpointOrder 1 < value := by
  have hmain := p.failed_window_estimate_of_valuation π v hπ hvπ hO hc i degree Ω hfail hdegree
  have hgap := kernel_threshold_gap (fun j : Fin n => D.weight j.val) D.exponent D.threshold
    (fun j => D.ratio_order_pos j.val)
    (fun k hk _ => D.threshold_ge_two_exponent hk)
    (Nat.succ_pos i.val) (p.failedCut_le_checkCut i) (p.checkCut_le i)
  rw [← D.endpointOrder_eq_remainingValue n (p.checkCut i) (p.checkCut_le i),
    ← D.endpointOrder_eq_remainingValue n 1 (by have hi := i.isLt; omega)] at hgap
  linarith

/-- Lemma X's estimate for one literal source product, with all source
endpoint and threshold hypotheses discharged from SourceBlockData. -/
theorem failed_window_estimate (π : O)
    (hπ : (π : K) = (D.uniformizer : K))
    (hO : ∀ a : O, D.valuation (a : K) ≤ 1) (hc : p.coefficient ≠ 0)
    (i : Fin n) (degree : ℕ) (Ω : ℝ)
    (hfail : correctedDigit p.formalExponent i ∉ digitInterval degree)
    (hdegree : 3 * (D.exponent : ℝ) * (2 * D.threshold (i.val + 1) + Ω) ≤
      (degree : ℝ) * D.weight i.val) :
    D.threshold (p.checkCut i) + D.threshold (i.val + 1) + Ω ≤
      levelValue (fun j : Fin n => D.weight j.val) D.exponent
        (realValuationOrder (coefficientFractionValuation O D.valuation) (p.formalCoefficient π))
        p.formalExponent (p.checkCut i) := by
  rw [p.formalExponent_eq_kernelProductExponent] at hfail ⊢
  rw [p.formalCoefficient_order_eq_kernelProductCoefficient π hπ hc]
  exact kernelProduct_failed_window_estimate
    (fun j => (D.ratio_order_pos j.val).le)
    (by exact_mod_cast D.exponent_pos)
    (fun j => (D.weight_lt_exponent j.val).le)
    (fun k hk => by
      change 1 ≤ remainingValue (fun j : Fin n => D.weight j.val) D.exponent k
      rw [← D.endpointOrder_eq_remainingValue n k hk]
      exact D.endpoint_order_ge_one k)
    (fun k hk _ => D.threshold_ge_two_exponent hk)
    (realValuationOrder D.valuation (p.coefficient : K))
    ((realValuationOrder_nonneg_iff D.valuation (Subtype.coe_ne_coe.mpr hc)).mpr
      (hO p.coefficient))
    p.variablePowers p.endpointPowers p.kernelGenerators i degree Ω hfail hdegree

/-- The literal source product clears the Z₁J₀ threshold after the supplied
previous-basis loss. No independent product-count or coefficient hypotheses
replace the actual FormalProduct data. -/
theorem after_loss (π : O)
    (hπ : (π : K) = (D.uniformizer : K))
    (hO : ∀ a : O, D.valuation (a : K) ≤ 1) (hc : p.coefficient ≠ 0)
    (i : Fin n) (degree : ℕ) (Ω value : ℝ)
    (hfail : correctedDigit p.formalExponent i ∉ digitInterval degree)
    (hdegree : 3 * (D.exponent : ℝ) * (2 * D.threshold (i.val + 1) + Ω) ≤
      (degree : ℝ) * D.weight i.val)
    (hloss : levelValue (fun j : Fin n => D.weight j.val) D.exponent
        (realValuationOrder (coefficientFractionValuation O D.valuation) (p.formalCoefficient π))
        p.formalExponent (p.checkCut i) - Ω ≤ value) :
    D.threshold (p.checkCut i) + D.endpointOrder (p.checkCut i) + D.endpointOrder 1 < value := by
  have hmain := p.failed_window_estimate π hπ hO hc i degree Ω hfail hdegree
  have hgap := kernel_threshold_gap (fun j : Fin n => D.weight j.val) D.exponent D.threshold
    (fun j => D.ratio_order_pos j.val)
    (fun k hk _ => D.threshold_ge_two_exponent hk)
    (Nat.succ_pos i.val) (p.failedCut_le_checkCut i) (p.checkCut_le i)
  rw [← D.endpointOrder_eq_remainingValue n (p.checkCut i) (p.checkCut_le i),
    ← D.endpointOrder_eq_remainingValue n 1 (by have hi := i.isLt; omega)] at hgap
  linarith

end FormalProduct
end SourceBlockData
end HereditaryAtomicity.DVRBase
