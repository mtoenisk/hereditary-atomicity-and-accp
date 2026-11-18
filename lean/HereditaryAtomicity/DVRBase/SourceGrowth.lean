import HereditaryAtomicity.DVRBase.SourceTransfer
import HereditaryAtomicity.DVRBase.KernelReflection
import HereditaryAtomicity.DVRBase.KernelControl

/-!
# Arbitrary-block source certificates

The kernel inclusion and selected-tail obstruction depend on the numerical growth and basis bounds, not on how
the blocks were chosen. The source comparison needs valuation/norm compatibility
only on the actual ratios; completion fields and maps remain explicit inputs.
The recursive certificate is a specialization of this single general proof.
-/

noncomputable section
namespace HereditaryAtomicity.DVRBase.SourceBlockData
open scoped BigOperators NNReal
variable {K k E : Type*} [Field K] [NontriviallyNormedField k] [CompleteSpace k]
  [NormedField E] [NormedAlgebra k E] [IsUltrametricDist E]
  {R : Subring K} (D : SourceBlockData R)

/-- Kernel control: exact source-kernel control for arbitrary blocks satisfying the growth bound.
The commuting coefficient square does not identify the valuation on all of `K`;
`hgw` explicitly identifies it on the selected ratios, which is all this proof uses.
No containment of `R` in the valuation ring or of `O` in `R` is assumed. -/
theorem source_kernel_mem_of_growth
    (y : ℕ → Eˣ) (hy : ∀ j, IsAlgebraic k (y j : E))
    (C : ℕ → ℝ) (hC : ∀ j, 1 ≤ C j)
    (hb : ∀ j (z : movingField k y j) i,
      ‖(movingTowerBasis k y hy j).repr z i • movingTowerBasis k y hy j i‖ ≤ C j * ‖z‖)
    (hgrowth : ∀ j, 3 * (D.exponent : ℝ) * (2 * D.threshold (j + 1) + Real.log (C j)) ≤
      (movingDegree k y j : ℝ) * D.weight j)
    (O : Subring K) (πO : O) (hπ : (πO : K) = (D.uniformizer : K))
    (hO : ∀ a : O, D.valuation (a : K) ≤ 1)
    (v : Valuation k ℝ≥0) (hv : ∀ a : k, realValuationOrder v a = -Real.log ‖a‖)
    (f : FractionRing O →+* k)
    (hf : ∀ a, v (f a) = coefficientFractionValuation O D.valuation a)
    (g : K →+* E) (hgy : ∀ j, (y j : E) = g (D.ratio j : K))
    (hgw : ∀ j, realValuationOrder D.valuation (D.ratio j : K) =
      -Real.log ‖g (D.ratio j : K)‖)
    (hcoeff : (algebraMap k E).comp f = g.comp (coefficientFractionEmbedding O)) :
    ∀ n, 0 < n → ∀ p : Laurent (FractionRing O) n,
      p ∈ D.formalRing O πO n → D.evaluation O n p = 0 →
        p ∈ modelKernelJunk (coefficientFractionValuation O D.valuation)
          (algebraMap O (FractionRing O) πO) (D.modelParameters n) := by
  intro n _ p hp hzero
  have hweight : ∀ j, D.weight j = -Real.log ‖(y j : E)‖ := by
    intro j
    rw [hgy j]
    exact hgw _
  have hz := movingTowerEval_map_eq_zero_of_source D O f g y hcoeff hgy n p hzero
  have hmem := D.kernel_formal_mem_of_growth y hy hweight C hC hb hgrowth πO hπ hO v hv f hf
    p hp hz
  exact (laurentMap_mem_modelKernelJunk_iff f (coefficientFractionValuation O D.valuation) v hf
    (algebraMap O (FractionRing O) πO) (D.coefficientUniformizer_ne_zero O πO hπ)
    (D.coefficientUniformizer_order O πO hπ) (D.modelParameters n) p).mp hmem

/-- The selected-tail obstruction for arbitrary source blocks satisfying the degree-growth inequality, with a selected cofinal tail.
The completion data and ratio-order compatibility `hgw` remain explicit inputs.
No `R ⊆ V`, uniformizer divisibility of the endpoints in `R`, or `O ≤ R` is needed;
the last hypothesis is needed only to conclude containment in `R`. -/
theorem exists_source_certificate_of_growth
    (y : ℕ → Eˣ) (hy : ∀ j, IsAlgebraic k (y j : E))
    (C : ℕ → ℝ) (hC : ∀ j, 1 ≤ C j)
    (hb : ∀ j (z : movingField k y j) i,
      ‖(movingTowerBasis k y hy j).repr z i • movingTowerBasis k y hy j i‖ ≤ C j * ‖z‖)
    (hgrowth : ∀ j, 3 * (D.exponent : ℝ) * (2 * D.threshold (j + 1) + Real.log (C j)) ≤
      (movingDegree k y j : ℝ) * D.weight j)
    (O : Subring K) [IsDiscreteValuationRing O] (πO : O) (hπirr : Irreducible πO)
    (hπ : (πO : K) = (D.uniformizer : K))
    (hO : ∀ a : O, D.valuation (a : K) ≤ 1)
    (v : Valuation k ℝ≥0) (hv : ∀ a : k, realValuationOrder v a = -Real.log ‖a‖)
    (f : FractionRing O →+* k)
    (hf : ∀ a, v (f a) = coefficientFractionValuation O D.valuation a)
    (g : K →+* E) (hgy : ∀ j, (y j : E) = g (D.ratio j : K))
    (hgw : ∀ j, realValuationOrder D.valuation (D.ratio j : K) =
      -Real.log ‖g (D.ratio j : K)‖)
    (hcoeff : (algebraMap k E).comp f = g.comp (coefficientFractionEmbedding O)) :
    ∃ Λ : Set ℕ, (∃ N : ℕ, 1 ≤ N ∧ Λ = Set.Ici N) ∧
      0 ∉ Λ ∧ (∀ m : ℕ, ∃ l, m ≤ l ∧ l ∈ Λ) ∧
      D.NoOutsideJunkFactorization O Λ ∧
      ¬ Factorization.IsAtomicDomain (D.sourceSubring O Λ) :=
  D.exists_source_certificate_of_kernel O πO hπirr hπ hO
    (D.source_kernel_mem_of_growth y hy C hC hb hgrowth O πO hπ hO v hv f hf g hgy hgw hcoeff)

/-- The selected-tail obstruction for every admissible selected tail of any growth-controlled block data.
The admissibility budget is over arbitrary finite subsets of the selected indices;
there is no requirement that the tail be the one chosen by the recursion. -/
theorem source_certificate_of_growth
    (y : ℕ → Eˣ) (hy : ∀ j, IsAlgebraic k (y j : E))
    (C : ℕ → ℝ) (hC : ∀ j, 1 ≤ C j)
    (hb : ∀ j (z : movingField k y j) i,
      ‖(movingTowerBasis k y hy j).repr z i • movingTowerBasis k y hy j i‖ ≤ C j * ‖z‖)
    (hgrowth : ∀ j, 3 * (D.exponent : ℝ) * (2 * D.threshold (j + 1) + Real.log (C j)) ≤
      (movingDegree k y j : ℝ) * D.weight j)
    (O : Subring K) [IsDiscreteValuationRing O] (πO : O) (hπirr : Irreducible πO)
    (hπ : (πO : K) = (D.uniformizer : K))
    (hO : ∀ a : O, D.valuation (a : K) ≤ 1)
    (v : Valuation k ℝ≥0) (hv : ∀ a : k, realValuationOrder v a = -Real.log ‖a‖)
    (f : FractionRing O →+* k)
    (hf : ∀ a, v (f a) = coefficientFractionValuation O D.valuation a)
    (g : K →+* E) (hgy : ∀ j, (y j : E) = g (D.ratio j : K))
    (hgw : ∀ j, realValuationOrder D.valuation (D.ratio j : K) =
      -Real.log ‖g (D.ratio j : K)‖)
    (hcoeff : (algebraMap k E).comp f = g.comp (coefficientFractionEmbedding O))
    (Λ : Set ℕ) (hΛ : D.AdmissibleTail Λ) :
    D.NoOutsideJunkFactorization O Λ ∧
      ¬ Factorization.IsAtomicDomain (D.sourceSubring O Λ) :=
  D.source_certificate_of_kernel O πO hπirr hπ hO Λ hΛ
    (D.source_kernel_mem_of_growth y hy C hC hb hgrowth O πO hπ hO v hv f hf g hgy hgw hcoeff)

end HereditaryAtomicity.DVRBase.SourceBlockData
