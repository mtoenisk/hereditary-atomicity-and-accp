import HereditaryAtomicity.DVRBase.CanonicalSourceCompletion

/-!
# Completion-free growth certificates for supplied blocks

The growth contract uses the canonical completions and the actual supplied
ratios. The moving-basis and degree-growth bounds provide the quantitative estimates.
All fields, maps, algebraicity proofs, and norm comparisons are constructed.
-/

noncomputable section
namespace HereditaryAtomicity.DVRBase.SourceBlockData
open scoped NNReal

variable {K : Type*} [Field K] {R : Subring K} (D : SourceBlockData R)
  (O : Subring K) [Algebra.IsAlgebraic O K]

attribute [local instance] canonicalFractionAlgebra canonicalCompletionAlgebra

/-- The moving-basis bound and the degree-growth inequality for the actual blocks in their canonical
completions. This does not postulate completion fields or their existence. -/
def CanonicalGrowth : Prop :=
  ∃ C : ℕ → ℝ, (∀ j, 1 ≤ C j) ∧
    (∀ j (z : movingField (D.CanonicalCoefficientField O) D.canonicalRatios j) i,
      ‖(movingTowerBasis (D.CanonicalCoefficientField O) D.canonicalRatios
        (D.canonicalRatios_algebraic O) j).repr z i •
        movingTowerBasis (D.CanonicalCoefficientField O) D.canonicalRatios
          (D.canonicalRatios_algebraic O) j i‖ ≤ C j * ‖z‖) ∧
    ∀ j, 3 * (D.exponent : ℝ) * (2 * D.threshold (j + 1) + Real.log (C j)) ≤
      (movingDegree (D.CanonicalCoefficientField O) D.canonicalRatios j : ℝ) * D.weight j

/-- Kernel control for supplied source blocks under the canonical moving-basis and degree-growth bounds. No
separately supplied completed fields, maps, or ratio norm identities remain. -/
theorem source_kernel_mem_of_canonicalGrowth
    (π : O) (hπ : (π : K) = (D.uniformizer : K))
    (hO : ∀ a : O, D.valuation (a : K) ≤ 1) (hG : D.CanonicalGrowth O) :
    ∀ n, 0 < n → ∀ p : Laurent (FractionRing O) n,
      p ∈ D.formalRing O π n → D.evaluation O n p = 0 →
        p ∈ modelKernelJunk (coefficientFractionValuation O D.valuation)
          (algebraMap O (FractionRing O) π) (D.modelParameters n) := by
  let := D.canonicalCoefficientNorm O π hπ
  obtain ⟨C, hC, hb, hgrowth⟩ := hG
  exact D.source_kernel_mem_of_growth D.canonicalRatios (D.canonicalRatios_algebraic O)
    C hC hb hgrowth O π hπ hO (completionValuation (coefficientFractionValuation O D.valuation))
    (completionValuation_order _) (algebraMap (FractionRing O) (D.CanonicalCoefficientField O))
    (completionValuation_algebraMap _) (algebraMap K D.CanonicalAmbientField)
    (D.canonicalRatios_val) (D.canonicalRatios_order) (D.canonical_coefficient_square O)

/-- The selected-tail obstruction for every prescribed admissible tail of the supplied source blocks,
using their canonical completions internally. -/
theorem source_certificate_of_canonicalGrowth
    [IsDiscreteValuationRing O] (π : O) (hπirr : Irreducible π)
    (hπ : (π : K) = (D.uniformizer : K))
    (hO : ∀ a : O, D.valuation (a : K) ≤ 1) (hG : D.CanonicalGrowth O)
    (Λ : Set ℕ) (hΛ : D.AdmissibleTail Λ) :
    D.NoOutsideJunkFactorization O Λ ∧
      ¬ Factorization.IsAtomicDomain (D.sourceSubring O Λ) :=
  D.source_certificate_of_kernel O π hπirr hπ hO Λ hΛ
    (D.source_kernel_mem_of_canonicalGrowth O π hπ hO hG)

/-- The canonical arbitrary-block contract also supplies a cofinal final
segment when the selected admissible tail is not prescribed in advance. -/
theorem exists_source_certificate_of_canonicalGrowth
    [IsDiscreteValuationRing O] (π : O) (hπirr : Irreducible π)
    (hπ : (π : K) = (D.uniformizer : K))
    (hO : ∀ a : O, D.valuation (a : K) ≤ 1) (hG : D.CanonicalGrowth O) :
    ∃ Λ : Set ℕ, (∃ N : ℕ, 1 ≤ N ∧ Λ = Set.Ici N) ∧
      0 ∉ Λ ∧ (∀ m : ℕ, ∃ l, m ≤ l ∧ l ∈ Λ) ∧
      D.NoOutsideJunkFactorization O Λ ∧
      ¬ Factorization.IsAtomicDomain (D.sourceSubring O Λ) :=
  D.exists_source_certificate_of_kernel O π hπirr hπ hO
    (D.source_kernel_mem_of_canonicalGrowth O π hπ hO hG)

/-- With coefficient containment, the same literal source cut lies in the
original source and is bounded for its given valuation. -/
theorem source_certificate_and_containment_of_canonicalGrowth
    [IsDiscreteValuationRing O] (π : O) (hπirr : Irreducible π)
    (hπ : (π : K) = (D.uniformizer : K)) (hOR : O ≤ R)
    (hO : ∀ a : O, D.valuation (a : K) ≤ 1) (hG : D.CanonicalGrowth O)
    (Λ : Set ℕ) (hΛ : D.AdmissibleTail Λ) :
    D.NoOutsideJunkFactorization O Λ ∧
      ¬ Factorization.IsAtomicDomain (D.sourceSubring O Λ) ∧
      D.sourceSubring O Λ ≤ R ∧ O ≤ D.sourceSubring O Λ ∧
      ∀ x : D.sourceSubring O Λ, D.valuation (x : K) ≤ 1 := by
  obtain ⟨hno, hna⟩ := D.source_certificate_of_canonicalGrowth O π hπirr hπ hO hG Λ hΛ
  exact ⟨hno, hna, D.sourceSubring_le O hOR Λ, D.coefficient_le_sourceSubring O Λ,
    D.sourceSubring_bounded O hO Λ⟩

end HereditaryAtomicity.DVRBase.SourceBlockData
