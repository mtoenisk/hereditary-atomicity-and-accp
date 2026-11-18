import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.Galois.Basic

/-!
# Valuation extensions through a normal closure
-/

/-! A finite Galois overfield for a finite separable extension. -/

namespace HereditaryAtomicity.ValuationAlgebra

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- The normal closure inside an algebraic closure of the upstairs field is
Galois when the original finite extension is separable. The ambient algebraic
closure itself need not be separable over the base field. -/
theorem isGalois_normalClosure_separable [FiniteDimensional K L]
    [Algebra.IsSeparable K L] :
    IsGalois K (IntermediateField.normalClosure K L (AlgebraicClosure L)) := by
  have hsep : ∀ f : L →ₐ[K] AlgebraicClosure L, Algebra.IsSeparable K f.fieldRange :=
    fun f => AlgEquiv.Algebra.isSeparable f.equivFieldRange
  have := hsep
  have : Algebra.IsSeparable K (IntermediateField.normalClosure K L (AlgebraicClosure L)) :=
    IntermediateField.isSeparable_iSup K (AlgebraicClosure L)
  exact {}

end HereditaryAtomicity.ValuationAlgebra
