import HereditaryAtomicity.SparseProductCut
import Mathlib.Analysis.Normed.Field.WithAbs
import Mathlib.Analysis.Normed.Field.Instances
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Analysis.Normed.Module.Completion
import Mathlib.Analysis.Normed.Algebra.Ultra
import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.Topology.Algebra.Valued.NormedValued

/-!
# The norm and completion attached to a real valuation

The absolute value below retains the literal nonnegative-real valuation, not
an arbitrary equivalent norm. Thus its negative logarithm agrees exactly with
the project's `realValuationOrder`, including that function's convention at
zero. Inequalities using finite additive order still require nonzero terms.
-/

noncomputable section
namespace HereditaryAtomicity.DVRBase

open scoped NNReal

variable {K : Type*} [Field K]

/-- Regard a nonnegative-real valuation as a real absolute value. -/
def valuationAbsoluteValue (v : Valuation K ℝ≥0) : AbsoluteValue K ℝ where
  toFun x := v x
  map_mul' x y := by simp
  nonneg' _ := NNReal.coe_nonneg _
  eq_zero' x := by simp
  add_le' x y := by
    have h : (v (x + y) : ℝ) ≤ max (v x : ℝ) (v y : ℝ) := by
      exact_mod_cast v.map_add_le_max' x y
    exact h.trans (max_le_add_of_nonneg (NNReal.coe_nonneg _) (NNReal.coe_nonneg _))

@[simp] theorem valuationAbsoluteValue_apply (v : Valuation K ℝ≥0) (x : K) :
    valuationAbsoluteValue v x = (v x : ℝ) := rfl

/-- A type synonym carrying exactly the norm prescribed by the valuation. -/
abbrev WithValuationNorm (v : Valuation K ℝ≥0) := WithAbs (valuationAbsoluteValue v)

@[simp] theorem norm_toAbs_valuation (v : Valuation K ℝ≥0) (x : K) :
    ‖WithAbs.toAbs (valuationAbsoluteValue v) x‖ = (v x : ℝ) := rfl

theorem realValuationOrder_eq_neg_log_norm (v : Valuation K ℝ≥0) (x : K) :
    realValuationOrder v x = -Real.log ‖WithAbs.toAbs (valuationAbsoluteValue v) x‖ := rfl

instance valuationNorm_isUltrametric (v : Valuation K ℝ≥0) :
    IsUltrametricDist (WithValuationNorm v) := by
  apply IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm
  intro x y
  change (v (x.ofAbs + y.ofAbs) : ℝ) ≤ max (v x.ofAbs : ℝ) (v y.ofAbs : ℝ)
  exact_mod_cast v.map_add_le_max' x.ofAbs y.ofAbs

/-- A nonzero element of valuation strictly below one makes the literal norm
nontrivial. This is the form supplied by a normalized uniformizer. -/
@[instance_reducible]
def valuationNorm_nontriviallyNormedField (v : Valuation K ℝ≥0)
    {π : K} (hπ : π ≠ 0) (hvπ : v π < 1) :
    NontriviallyNormedField (WithValuationNorm v) :=
  NontriviallyNormedField.ofNormNeOne ⟨WithAbs.toAbs (valuationAbsoluteValue v) π,
    by simpa using hπ, by simpa using (show (v π : ℝ) < 1 by exact_mod_cast hvπ).ne⟩

/-- The completion retains its canonical embedding of the original field. -/
abbrev ValuationNormCompletion (v : Valuation K ℝ≥0) :=
  (valuationAbsoluteValue v).Completion

instance valuationNormCompletion_isUltrametric (v : Valuation K ℝ≥0) :
    IsUltrametricDist (ValuationNormCompletion v) :=
  IsUltrametricDist.of_normedAlgebra (WithValuationNorm v)
    (L := ValuationNormCompletion v)

/-- The nonnegative-real valuation on the completed normed field. -/
def completionValuation (v : Valuation K ℝ≥0) :
    Valuation (ValuationNormCompletion v) ℝ≥0 := NormedField.valuation

@[simp] theorem completionValuation_apply (v : Valuation K ℝ≥0)
    (x : ValuationNormCompletion v) : completionValuation v x = ‖x‖₊ := rfl

theorem completionValuation_order (v : Valuation K ℝ≥0)
    (x : ValuationNormCompletion v) :
    realValuationOrder (completionValuation v) x = -Real.log ‖x‖ := rfl

@[simp] theorem norm_completion_valuation (v : Valuation K ℝ≥0) (x : K) :
    ‖(algebraMap K (ValuationNormCompletion v)) x‖ = (v x : ℝ) := by
  change ‖(WithAbs.toAbs (valuationAbsoluteValue v) x : ValuationNormCompletion v)‖ = _
  simp

theorem realValuationOrder_eq_neg_log_completion_norm
    (v : Valuation K ℝ≥0) (x : K) :
    realValuationOrder v x =
      -Real.log ‖(algebraMap K (ValuationNormCompletion v)) x‖ := by
  rw [norm_completion_valuation]
  rfl

@[simp] theorem completionValuation_algebraMap (v : Valuation K ℝ≥0) (x : K) :
    completionValuation v (algebraMap K (ValuationNormCompletion v) x) = v x := by
  apply NNReal.coe_injective
  exact norm_completion_valuation v x

/-- The completed field is nontrivially normed whenever the original valuation
has a nonzero element of value below one. -/
@[instance_reducible]
def valuationNormCompletion_nontriviallyNormedField (v : Valuation K ℝ≥0)
    {π : K} (hπ : π ≠ 0) (hvπ : v π < 1) :
    NontriviallyNormedField (ValuationNormCompletion v) :=
  NontriviallyNormedField.ofNormNeOne
    ⟨algebraMap K (ValuationNormCompletion v) π,
      (map_ne_zero_iff _ (algebraMap K (ValuationNormCompletion v)).injective).mpr hπ,
      by simpa using (show (v π : ℝ) < 1 by exact_mod_cast hvπ).ne⟩

/-- Completion of an ultrametric field introduces no new nonzero norm values:
a sufficiently close original element has the same norm. -/
theorem exists_source_norm_eq_completion (v : Valuation K ℝ≥0)
    (x : ValuationNormCompletion v) (hx : x ≠ 0) :
    ∃ a : K, a ≠ 0 ∧ ‖x‖ = (v a : ℝ) := by
  obtain ⟨a, ha⟩ := UniformSpace.Completion.denseRange_coe.exists_dist_lt x
    (norm_pos_iff.mpr hx)
  have hclose : ‖x + -(a : ValuationNormCompletion v)‖ <
      max ‖x‖ ‖-(a : ValuationNormCompletion v)‖ := by
    rw [← sub_eq_add_neg, ← dist_eq_norm]
    exact ha.trans_le (le_max_left _ _)
  have he : ‖x‖ = ‖(a : ValuationNormCompletion v)‖ := by
    simpa only [norm_neg] using IsUltrametricDist.norm_eq_of_add_norm_lt_max hclose
  have he' : ‖x‖ = (v a.ofAbs : ℝ) := by
    simpa only [UniformSpace.Completion.norm_coe, WithAbs.norm_eq_apply_ofAbs,
      valuationAbsoluteValue_apply] using he
  refine ⟨a.ofAbs, ?_, he'⟩
  intro ha0
  have : ‖x‖ = 0 := by simpa [ha0] using he'
  exact hx (norm_eq_zero.mp this)

/-- The integer-valued additive order on the base field remains integer valued on the
nonzero elements of its completion. -/
theorem completion_order_integral (v : Valuation K ℝ≥0)
    (h : ∀ a : K, a ≠ 0 → ∃ z : ℤ, realValuationOrder v a = z)
    (x : ValuationNormCompletion v) (hx : x ≠ 0) :
    ∃ z : ℤ, -Real.log ‖x‖ = z := by
  obtain ⟨a, ha, he⟩ := exists_source_norm_eq_completion v x hx
  obtain ⟨z, hz⟩ := h a ha
  exact ⟨z, by simpa only [he, realValuationOrder] using hz⟩

section Extension

variable {L : Type*} [Field L] [Algebra K L]
  (v : Valuation K ℝ≥0) (w : Valuation L ℝ≥0)
  (h : ∀ x : K, w (algebraMap K L x) = v x)

include h

/-- Literal extension of valuations gives literal extension of absolute values. -/
theorem valuationAbsoluteValue_liesOver :
    (valuationAbsoluteValue w).LiesOver (valuationAbsoluteValue v) where
  under_eq := by
    ext x
    exact congrArg (fun t : ℝ≥0 => (t : ℝ)) (h x)

/-- The base completion embeds isometrically in the ambient completion through
the canonical extension of the original algebra map. -/
@[instance_reducible]
def valuationCompletionNormedAlgebra :
    NormedAlgebra (ValuationNormCompletion v) (ValuationNormCompletion w) := by
  let : (valuationAbsoluteValue w).LiesOver (valuationAbsoluteValue v) :=
    valuationAbsoluteValue_liesOver v w h
  let A := AbsoluteValue.Completion.algebraOfLiesOver
    (valuationAbsoluteValue v) (valuationAbsoluteValue w)
  let : Algebra (ValuationNormCompletion v) (ValuationNormCompletion w) := A
  refine { A with norm_smul_le := ?_ }
  intro r x
  rw [Algebra.smul_def, norm_mul]
  have hr : ‖algebraMap (ValuationNormCompletion v) (ValuationNormCompletion w) r‖ = ‖r‖ := by
    apply (AddMonoidHomClass.isometry_iff_norm _).mp
    exact UniformSpace.Completion.isometry_mapRingHom
      (WithAbs.isometry_map (valuationAbsoluteValue v) (valuationAbsoluteValue w))
  rw [hr]

/-- The completed algebra map agrees with the original field map. -/
theorem valuationCompletion_scalarTower :
    letI := valuationCompletionNormedAlgebra v w h
    IsScalarTower K (ValuationNormCompletion v) (ValuationNormCompletion w) := by
  let : (valuationAbsoluteValue w).LiesOver (valuationAbsoluteValue v) :=
    valuationAbsoluteValue_liesOver v w h
  let := AbsoluteValue.Completion.algebraOfLiesOver
    (valuationAbsoluteValue v) (valuationAbsoluteValue w)
  change IsScalarTower K (ValuationNormCompletion v) (ValuationNormCompletion w)
  infer_instance

/-- The completed ambient valuation restricts to the completed base valuation
without any rescaling. -/
theorem completionValuation_restrict :
    letI := valuationCompletionNormedAlgebra v w h
    ∀ x : ValuationNormCompletion v,
      completionValuation w
        (algebraMap (ValuationNormCompletion v) (ValuationNormCompletion w) x) =
      completionValuation v x := by
  let := valuationCompletionNormedAlgebra v w h
  intro x
  apply NNReal.coe_injective
  exact norm_algebraMap' (ValuationNormCompletion w) x

/-- An element algebraic over the original base remains algebraic over the
completed base inside the ambient completion. -/
theorem isAlgebraic_completion_source (x : L) (hx : IsAlgebraic K x) :
    letI := valuationCompletionNormedAlgebra v w h
    IsAlgebraic (ValuationNormCompletion v)
      (algebraMap L (ValuationNormCompletion w) x) := by
  let := valuationCompletionNormedAlgebra v w h
  let := valuationCompletion_scalarTower v w h
  have hx' : IsAlgebraic K (algebraMap L (ValuationNormCompletion w) x) :=
    hx.algebraMap
  exact hx'.tower_top (L := ValuationNormCompletion v)

/-- Finitely many algebraic source elements generate a finite field extension
of the completed base in the ambient completion. -/
theorem finiteDimensional_completion_adjoin (s : Finset L)
    (hs : ∀ x ∈ s, IsAlgebraic K x) :
    letI := valuationCompletionNormedAlgebra v w h
    FiniteDimensional (ValuationNormCompletion v)
      (IntermediateField.adjoin (ValuationNormCompletion v)
        ((algebraMap L (ValuationNormCompletion w)) '' (s : Set L))) := by
  classical
  let := valuationCompletionNormedAlgebra v w h
  let : Fintype ((algebraMap L (ValuationNormCompletion w)) '' (s : Set L)) :=
    (s.finite_toSet.image _).fintype
  apply IntermediateField.finiteDimensional_adjoin
  rintro y ⟨x, hx, rfl⟩
  exact (isAlgebraic_completion_source v w h x (hs x hx)).isIntegral

end Extension

end HereditaryAtomicity.DVRBase
