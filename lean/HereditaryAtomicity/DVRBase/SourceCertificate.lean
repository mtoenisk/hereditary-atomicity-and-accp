import HereditaryAtomicity.DVRBase.SourceGrowth

/-!
# The constructed source certificate

The actual block recursion supplies the moving-basis kernel theorem. Exact
coefficient/source evaluation compatibility and support reflection transfer
that theorem back to the original DVR coefficient field. The resulting
literal selected source subring has a cofinal tail, no endpoint factorization
by elements outside its actual junk set, and is not atomic.
-/

noncomputable section
namespace HereditaryAtomicity.DVRBase.BlockInput
open scoped BigOperators NNReal
variable {K k E : Type*} [Field K] [NontriviallyNormedField k] [CompleteSpace k]
  [NormedField E] [NormedAlgebra k E] [IsUltrametricDist E]
  {R : Subring K} {π : R} {t : ℕ → R}
  (I : BlockInput R k E π t) (w : Valuation K ℝ≥0)
  (hw : ∀ r : R, I.valuation (I.embedding r) = w (r : K))
  (hcompat : ∀ x : E, realValuationOrder I.valuation x = -Real.log ‖x‖)

local notation "D" => I.toSourceBlockData BlockState.basisLoss w hw

include hcompat

/-- Exact kernel control over the original coefficient field, derived from
the actual constructed moving basis and the commuting source embeddings. -/
theorem source_kernel_mem
    (O : Subring K) (πO : O) (hπ : (πO : K) = (π : K))
    (hO : ∀ a : O, w (a : K) ≤ 1)
    (v : Valuation k ℝ≥0) (hv : ∀ a : k, realValuationOrder v a = -Real.log ‖a‖)
    (f : FractionRing O →+* k) (hf : ∀ a, v (f a) = coefficientFractionValuation O w a)
    (g : K →+* E) (hg : ∀ r : R, g (r : K) = I.embedding r)
    (hcoeff : (algebraMap k E).comp f = g.comp (coefficientFractionEmbedding O))
    {n : ℕ} (p : Laurent (FractionRing O) n) (hp : p ∈ (D).formalRing O πO n)
    (hzero : (D).evaluation O n p = 0) :
    p ∈ modelKernelJunk (coefficientFractionValuation O w)
      (algebraMap O (FractionRing O) πO) ((D).modelParameters n) := by
  have hy : ∀ j, (I.generator BlockState.basisLoss j : E) = g ((D).ratio j : K) := by
    intro j
    rw [I.generator_val_eq_embedding_sourceY]
    exact (hg (I.sourceY BlockState.basisLoss j)).symm
  have hz := movingTowerEval_map_eq_zero_of_source (D) O f g
    (I.generator BlockState.basisLoss) hcoeff hy n p hzero
  have hmem := I.kernel_formal_mem w hw hcompat πO hπ hO v hv f hf p hp hz
  exact (laurentMap_mem_modelKernelJunk_iff f (coefficientFractionValuation O w) v hf
    (algebraMap O (FractionRing O) πO) ((D).coefficientUniformizer_ne_zero O πO hπ)
    ((D).coefficientUniformizer_order O πO hπ) ((D).modelParameters n) p).mp hmem

/-- The selected-tail obstruction for the actual recursive source blocks. The source ring, selected
tail, ideal and no-factorization certificate are all the literal constructed
ones. No kernel-containment or finite-lift hypothesis remains. -/
theorem exists_source_certificate
    (O : Subring K) [IsDiscreteValuationRing O] (hOR : O ≤ R)
    (πO : O) (hπirr : Irreducible πO) (hπ : (πO : K) = (π : K))
    (hO : ∀ a : O, w (a : K) ≤ 1)
    (v : Valuation k ℝ≥0) (hv : ∀ a : k, realValuationOrder v a = -Real.log ‖a‖)
    (f : FractionRing O →+* k) (hf : ∀ a, v (f a) = coefficientFractionValuation O w a)
    (g : K →+* E) (hg : ∀ r : R, g (r : K) = I.embedding r)
    (hcoeff : (algebraMap k E).comp f = g.comp (coefficientFractionEmbedding O)) :
    ∃ Λ : Set ℕ, (∃ N : ℕ, 1 ≤ N ∧ Λ = Set.Ici N) ∧
      0 ∉ Λ ∧ (∀ m : ℕ, ∃ l, m ≤ l ∧ l ∈ Λ) ∧
      (D).NoOutsideJunkFactorization O Λ ∧
      ¬ Factorization.IsAtomicDomain ((D).sourceSubring O Λ) ∧
      (D).sourceSubring O Λ ≤ R ∧ O ≤ (D).sourceSubring O Λ := by
  have hgy : ∀ j, (I.generator BlockState.basisLoss j : E) = g ((D).ratio j : K) := by
    intro j
    rw [I.generator_val_eq_embedding_sourceY]
    exact (hg (I.sourceY BlockState.basisLoss j)).symm
  have hgw : ∀ j, realValuationOrder w ((D).ratio j : K) =
      -Real.log ‖g ((D).ratio j : K)‖ := by
    intro j
    rw [← hgy j]
    exact I.kernel_source_weight_norm w hw hcompat j
  obtain ⟨Λ, htail, hzero, hcofinal, hno, hnonatomic⟩ :=
    (D).exists_source_certificate_of_growth
      (I.generator BlockState.basisLoss) (I.generator_algebraic BlockState.basisLoss)
      I.selectedBasisConstant I.one_le_selectedBasisConstant I.selectedBasisConstant_spec
      (fun j => by
        rw [← I.omega_basisLoss_eq_log]
        exact I.actual_product_degree_growth w hw j)
      O πO hπirr hπ hO v hv f hf g hgy hgw hcoeff
  exact ⟨Λ, htail, hzero, hcofinal, hno, hnonatomic,
    (D).sourceSubring_le O hOR Λ, (D).coefficient_le_sourceSubring O Λ⟩

end HereditaryAtomicity.DVRBase.BlockInput
