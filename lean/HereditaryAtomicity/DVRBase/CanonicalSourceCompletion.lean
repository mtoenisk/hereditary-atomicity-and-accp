import HereditaryAtomicity.DVRBase.SourceGrowth
import HereditaryAtomicity.DVRBase.BaseValues
import HereditaryAtomicity.DVRBase.CoefficientExtension

/-!
# Canonical completions for supplied source blocks

These constructions retain the actual supplied source blocks. The coefficient
field is the completion of the coefficient fraction field with its restricted
valuation; the ambient field is the completion for the given source valuation.
No new blocks, field embeddings, or comparison hypotheses are chosen.
-/

noncomputable section
namespace HereditaryAtomicity.DVRBase.SourceBlockData
open scoped NNReal

variable {K : Type*} [Field K] {R : Subring K} (D : SourceBlockData R)
  (O : Subring K)

/-- The prescribed coefficient fraction field with its actual embedding. -/
@[instance_reducible] def canonicalFractionAlgebra : Algebra (FractionRing O) K :=
  (coefficientFractionEmbedding O).toAlgebra

attribute [local instance] canonicalFractionAlgebra

/-- The completed coefficient field, with no choice of an equivalent valuation. -/
abbrev CanonicalCoefficientField :=
  ValuationNormCompletion (coefficientFractionValuation O D.valuation)

/-- The completion of the actual ambient valued field. -/
abbrev CanonicalAmbientField := ValuationNormCompletion D.valuation

/-- The completed extension of the prescribed coefficient embedding. -/
@[instance_reducible] def canonicalCompletionAlgebra :
    NormedAlgebra (D.CanonicalCoefficientField O) D.CanonicalAmbientField :=
  valuationCompletionNormedAlgebra (coefficientFractionValuation O D.valuation)
    D.valuation (fun _ => rfl)

attribute [local instance] canonicalCompletionAlgebra

/-- Nontriviality is witnessed by the coefficient uniformizer already in the
source data. It is constructed rather than requested from the caller. -/
@[instance_reducible] def canonicalCoefficientNorm (π : O)
    (hπ : (π : K) = (D.uniformizer : K)) :
    NontriviallyNormedField (D.CanonicalCoefficientField O) := by
  have h0 := D.coefficientUniformizer_ne_zero O π hπ
  have hv : coefficientFractionValuation O D.valuation
      (algebraMap O (FractionRing O) π) < 1 :=
    (realValuationOrder_pos_iff _ h0).mp (by
      rw [D.coefficientUniformizer_order O π hπ]
      exact zero_lt_one)
  exact valuationNormCompletion_nontriviallyNormedField _ h0 hv

/-- Original algebraicity over the coefficient DVR passes to its fraction field. -/
theorem canonicalFraction_algebraic [Algebra.IsAlgebraic O K] (x : K) :
    IsAlgebraic (FractionRing O) x := by
  let : IsScalarTower O (FractionRing O) K :=
    IsScalarTower.of_algebraMap_eq fun z =>
      (coefficientFractionEmbedding_algebraMap O z).symm
  exact (Algebra.IsAlgebraic.isAlgebraic (R := O) x).extendScalars
    (IsFractionRing.injective O (FractionRing O))

/-- Canonical units obtained from the supplied nonzero source ratios. -/
def canonicalRatios (j : ℕ) : D.CanonicalAmbientFieldˣ :=
  Units.mk0 (algebraMap K D.CanonicalAmbientField (D.ratio j : K))
    ((algebraMap K D.CanonicalAmbientField).injective.ne
      (Subtype.coe_ne_coe.mpr (D.ratio_ne_zero j)))

@[simp] theorem canonicalRatios_val (j : ℕ) :
    (D.canonicalRatios j : D.CanonicalAmbientField) =
      algebraMap K D.CanonicalAmbientField (D.ratio j : K) := rfl

/-- Every canonical ratio is algebraic over the canonical completed coefficient
field. Algebraicity of the ambient completion is neither needed nor asserted. -/
theorem canonicalRatios_algebraic [Algebra.IsAlgebraic O K] (j : ℕ) :
    IsAlgebraic (D.CanonicalCoefficientField O)
      (D.canonicalRatios j : D.CanonicalAmbientField) :=
  isAlgebraic_completion_source (coefficientFractionValuation O D.valuation)
    D.valuation (fun _ => rfl) (D.ratio j : K) (canonicalFraction_algebraic O _)

/-- The norm identity applies to the actual supplied ratio, with no separately
assumed valuation comparison on the ambient field. -/
theorem canonicalRatios_order (j : ℕ) :
    D.weight j = -Real.log ‖(D.canonicalRatios j : D.CanonicalAmbientField)‖ :=
  realValuationOrder_eq_neg_log_completion_norm D.valuation (D.ratio j : K)

/-- The actual coefficient square commutes after canonical completion. -/
theorem canonical_coefficient_square :
    (algebraMap (D.CanonicalCoefficientField O) D.CanonicalAmbientField).comp
      (algebraMap (FractionRing O) (D.CanonicalCoefficientField O)) =
    (algebraMap K D.CanonicalAmbientField).comp (coefficientFractionEmbedding O) := by
  ext a
  exact coefficientCompletionEmbedding_algebraMap O D.valuation a

end HereditaryAtomicity.DVRBase.SourceBlockData
