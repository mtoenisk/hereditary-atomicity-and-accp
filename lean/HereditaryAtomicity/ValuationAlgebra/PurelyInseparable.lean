import HereditaryAtomicity.ValuationAlgebra.ExtensionFiber
import Mathlib.FieldTheory.PurelyInseparable.Basic

/-!
# Valuation extensions through purely inseparable fields
-/

/-! Positive-power descent for actual purely inseparable field extensions. -/

namespace HereditaryAtomicity.ValuationAlgebra

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- The reusable power-descent input follows from the standard field-extension
predicate, in every characteristic and without a finite-degree hypothesis. -/
theorem power_descent_of_purelyInseparable [IsPurelyInseparable K L] :
    ∀ x : L, ∃ (n : ℕ) (_ : n ≠ 0) (y : K), x ^ n = algebraMap K L y := by
  obtain ⟨q, _⟩ := ExpChar.exists K
  intro x
  obtain ⟨n, y, hy⟩ := IsPurelyInseparable.pow_mem K q x
  exact ⟨q ^ n, pow_ne_zero n (expChar_ne_zero K q), y, hy.symm⟩

/-- Purely inseparable restriction is injective on actual valuation subrings. -/
theorem comap_injective_of_purelyInseparable [IsPurelyInseparable K L] :
    Function.Injective (fun W : ValuationSubring L => W.comap (algebraMap K L)) :=
  comap_injective_of_power_descent (algebraMap K L) power_descent_of_purelyInseparable

end HereditaryAtomicity.ValuationAlgebra
