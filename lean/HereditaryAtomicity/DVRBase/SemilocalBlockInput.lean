import HereditaryAtomicity.DVRBase.SemilocalReduction
import HereditaryAtomicity.DVRBase.BlockConstruction
import HereditaryAtomicity.DVRBase.BaseValues
import HereditaryAtomicity.DVRBase.CoefficientExtension

/-!
# Canonical completed input from a semilocal source chain

The source ring remains the chosen maximal stalk. The original DVR and its
uniformizer, as well as the original-domain ratios and endpoints, remain the
ones constructed by `SemilocalChainSetup`. Only the coefficient fraction field
and the ambient valued field are completed.
-/

noncomputable section
namespace HereditaryAtomicity.DVRBase.SemilocalChainSetup
open scoped NNReal

variable {K : Type*} [Field K] {D : Subring K} [IsFractionRing D K]
  {M : MaximalSpectrum D} (H : SemilocalChainSetup D M)

/-- The literal restriction to the original coefficient fraction field. -/
abbrev fractionValuation : Valuation (FractionRing H.base) ℝ≥0 :=
  coefficientFractionValuation H.base H.valuation

/-- The canonical fraction-field algebra, with no chosen field isomorphism. -/
@[instance_reducible] def fractionAlgebra : Algebra (FractionRing H.base) K :=
  (coefficientFractionEmbedding H.base).toAlgebra

attribute [local instance] fractionAlgebra

@[simp] theorem fraction_algebraMap (a : FractionRing H.base) :
    algebraMap (FractionRing H.base) K a = coefficientFractionEmbedding H.base a := rfl

theorem base_bounded (a : H.base) : H.valuation (a : K) ≤ 1 :=
  H.bounded (Subring.inclusion H.base_le a)

theorem fraction_source_algebraic (x : K) : IsAlgebraic (FractionRing H.base) x := by
  let : Algebra.IsAlgebraic H.base K := H.base_algebraic
  let : IsScalarTower H.base (FractionRing H.base) K :=
    IsScalarTower.of_algebraMap_eq fun a => by
      exact (coefficientFractionEmbedding_algebraMap H.base a).symm
  exact (Algebra.IsAlgebraic.isAlgebraic (R := H.base) x).extendScalars
    (IsFractionRing.injective H.base (FractionRing H.base))

/-- Actual input before completion; the power-return witnesses remain in the
chosen stalk, where they were proved. -/
def originalBlockInput : BlockInput (sourceMaximalStalk D M) (FractionRing H.base) K
    (Subring.inclusion H.base_le H.uniformizer)
    (fun n => sourceMaximalMap D M (H.ratio n)) where
  chain := H.chain
  embedding := (sourceMaximalStalk D M).subtype
  embedding_injective := Subtype.val_injective
  valuation := H.valuation
  coefficient_orders a ha := by
    let : IsDiscreteValuationRing H.base := H.base_dvr
    exact coefficientFraction_order_integral H.base H.valuation H.base_bounded
      H.uniformizer_irreducible H.normalized ha
  source_algebraic r := H.fraction_source_algebraic (r : K)
  endpoint_order_ge_one := H.endpoint_order_ge_one
  uniformizer_order := H.normalized
  ratio_positive := H.ratio_order_pos

@[simp] theorem originalBlockInput_chain : H.originalBlockInput.chain = H.chain := rfl

@[simp] theorem originalBlockInput_embedding (r : sourceMaximalStalk D M) :
    H.originalBlockInput.embedding r = (r : K) := rfl

@[simp] theorem originalBlockInput_valuation : H.originalBlockInput.valuation = H.valuation := rfl

/-- The original coefficient uniformizer as an element of its fraction field. -/
def fractionUniformizer : FractionRing H.base :=
  algebraMap H.base (FractionRing H.base) H.uniformizer

theorem fractionUniformizer_ne_zero : H.fractionUniformizer ≠ 0 :=
  (map_ne_zero_iff _ (IsFractionRing.injective H.base (FractionRing H.base))).mpr
    H.uniformizer_irreducible.ne_zero

@[simp] theorem fractionUniformizer_order :
    realValuationOrder H.fractionValuation H.fractionUniformizer = 1 := by
  simpa only [fractionUniformizer, fractionValuation, coefficientFractionValuation,
    realValuationOrder, Valuation.comap_apply, coefficientFractionEmbedding_algebraMap]
    using H.normalized

theorem fractionUniformizer_value_lt_one : H.fractionValuation H.fractionUniformizer < 1 :=
  (realValuationOrder_pos_iff H.fractionValuation H.fractionUniformizer_ne_zero).mp
    (by rw [H.fractionUniformizer_order]; norm_num)

/-- The actual completed coefficient field has a nontrivial norm, witnessed
by the same uniformizer. -/
@[instance_reducible] def completedBaseNorm :
    NontriviallyNormedField (ValuationNormCompletion H.fractionValuation) :=
  valuationNormCompletion_nontriviallyNormedField H.fractionValuation
    H.fractionUniformizer_ne_zero H.fractionUniformizer_value_lt_one

/-- The isometric extension of the canonical original coefficient embedding. -/
@[instance_reducible] def completedAlgebra :
    NormedAlgebra (ValuationNormCompletion H.fractionValuation)
      (ValuationNormCompletion H.valuation) :=
  valuationCompletionNormedAlgebra H.fractionValuation H.valuation (fun _ => rfl)

attribute [local instance] completedAlgebra

/-- Literal completion of the fixed actual block input. -/
def completedBlockInput :
    BlockInput (sourceMaximalStalk D M) (ValuationNormCompletion H.fractionValuation)
      (ValuationNormCompletion H.valuation)
      (Subring.inclusion H.base_le H.uniformizer)
      (fun n => sourceMaximalMap D M (H.ratio n)) :=
  H.originalBlockInput.completed H.fractionValuation (fun _ => rfl)

@[simp] theorem completedBlockInput_chain : H.completedBlockInput.chain = H.chain := rfl

@[simp] theorem completedBlockInput_embedding (r : sourceMaximalStalk D M) :
    H.completedBlockInput.embedding r =
      algebraMap K (ValuationNormCompletion H.valuation) (r : K) := rfl

@[simp] theorem completedBlockInput_valuation :
    H.completedBlockInput.valuation = completionValuation H.valuation := rfl

/-- Exact valuation preservation on every source element. -/
theorem completedBlockInput_source_valuation (r : sourceMaximalStalk D M) :
    H.completedBlockInput.valuation (H.completedBlockInput.embedding r) =
      H.valuation (r : K) :=
  completionValuation_algebraMap H.valuation (r : K)

/-- The valuation is the order of the actual norm used by the moving bases. -/
theorem completedBlockInput_order (x : ValuationNormCompletion H.valuation) :
    realValuationOrder H.completedBlockInput.valuation x = -Real.log ‖x‖ := rfl

/-- Completing the coefficients preserves their exact valuation. -/
theorem coefficient_completion_valuation (a : FractionRing H.base) :
    completionValuation H.fractionValuation
      (algebraMap (FractionRing H.base) (ValuationNormCompletion H.fractionValuation) a) =
        coefficientFractionValuation H.base H.valuation a :=
  completionValuation_algebraMap H.fractionValuation a

/-- The coefficient square is an equality of actual ring homomorphisms. -/
theorem completed_coefficient_square :
    (algebraMap (ValuationNormCompletion H.fractionValuation)
      (ValuationNormCompletion H.valuation)).comp
        (algebraMap (FractionRing H.base) (ValuationNormCompletion H.fractionValuation)) =
    (algebraMap K (ValuationNormCompletion H.valuation)).comp
      (coefficientFractionEmbedding H.base) := by
  ext a
  exact coefficientCompletionEmbedding_algebraMap H.base H.valuation a

end HereditaryAtomicity.DVRBase.SemilocalChainSetup
