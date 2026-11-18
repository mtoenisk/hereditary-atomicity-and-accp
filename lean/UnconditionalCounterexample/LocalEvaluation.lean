import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.Topology.Algebra.Module.Cardinality
import Mathlib.Data.Rat.Encodable
import Mathlib.Data.Finsupp.Encodable
import Mathlib.Algebra.Polynomial.Cardinal

/-!
# Transcendental evaluation and local choice

Evaluation at a transcendental element embeds the rational-function field. Over a
complete nontrivially normed scalar field, each nonempty open subset of the given
space contains an element transcendental over the rationals.
-/

noncomputable section

namespace UnconditionalCounterexample.LocalEvaluation

open Polynomial IntermediateField

variable {F L : Type*} [Field F] [Field L] [Algebra F L]

/-- Evaluation into the ambient field through the simple intermediate field. -/
def evalAt (a : L) (ha : Transcendental F a) : RatFunc F →ₐ[F] L :=
  (IntermediateField.val F⟮a⟯).comp (RatFunc.algEquivOfTranscendental a ha).toAlgHom

/-- Transcendental evaluation has zero kernel. -/
theorem evalAt_injective (a : L) (ha : Transcendental F a) :
    Function.Injective (evalAt a ha) :=
  (evalAt a ha).injective

/-- The rational-function variable maps to the specified argument. -/
@[simp]
theorem evalAt_X (a : L) (ha : Transcendental F a) :
    evalAt a ha RatFunc.X = a := by
  simp [evalAt]

/-- Evaluation agrees with the numerator/denominator formula. -/
theorem evalAt_apply (a : L) (ha : Transcendental F a) (f : RatFunc F) :
    evalAt a ha f = aeval a f.num / aeval a f.denom := by
  exact RatFunc.algEquivOfTranscendental_apply a ha f

variable [Algebra ℚ L]

/-- There are only countably many rationally algebraic elements in a field. -/
theorem algebraic_countable : (Set.ofPred (IsAlgebraic ℚ : L → Prop)).Countable := by
  have : Countable ℚ[X] := (Polynomial.toFinsuppIso ℚ).injective.countable
  have h : Set.ofPred (IsAlgebraic ℚ : L → Prop) = ⋃ f : ℚ[X], f.rootSet L := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Polynomial.mem_rootSet]
    rfl
  rw [h]
  exact Set.countable_iUnion fun f => (f.rootSet_finite L).countable

/-- Rationally transcendental elements are dense in this topological vector space. -/
theorem transcendental_dense
    (K : Type*) [NontriviallyNormedField K] [CompleteSpace K]
    [Module K L] [TopologicalSpace L] [ContinuousAdd L] [ContinuousSMul K L] :
    Dense (Set.ofPred (Transcendental ℚ : L → Prop)) := by
  exact algebraic_countable.dense_compl K

/-- Any prescribed nonempty open set admits a rationally transcendental argument. -/
theorem exists_transcendental_mem_open
    (K : Type*) [NontriviallyNormedField K] [CompleteSpace K]
    [Module K L] [TopologicalSpace L] [ContinuousAdd L] [ContinuousSMul K L]
    {U : Set L} (hU : IsOpen U) (hne : U.Nonempty) :
    ∃ a ∈ U, Transcendental ℚ a := by
  obtain ⟨a, ha, htrans⟩ := (transcendental_dense (L := L) K).inter_open_nonempty U hU hne
  exact ⟨a, ha, htrans⟩

end UnconditionalCounterexample.LocalEvaluation
