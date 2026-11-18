import HereditaryAtomicity.ValuationAlgebra.IntegralClosure
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

/-! # Integral closure localizations in arbitrary algebraic extensions

Each fraction witness involves a single finite subextension. Thus the finite
valuation extension theorem applies without imposing finite degree on the
ambient extension or finite generation of its integral closure.
-/

namespace HereditaryAtomicity.ValuationAlgebra

variable {F K : Type*} [Field F] [Field K] [Algebra F K]
  [Algebra.IsAlgebraic F K]

/-- A prolongation in an arbitrary algebraic extension is the localization
of the entire integral closure at its actual center, expressed by fractions. -/
theorem mem_extension_iff_fraction_of_isAlgebraic
    (V : ValuationSubring F) [Algebra V K] [IsScalarTower V F K]
    (W : ValuationSubring K) (hW : W.comap (algebraMap F K) = V) (x : K) :
    x ∈ W ↔ ∃ a s : integralClosure V K,
      s ∉ prolongationCenter V W hW ∧ x = (a : K) / (s : K) := by
  constructor
  · intro hx
    let E := IntermediateField.adjoin F ({x} : Set K)
    let : FiniteDimensional F E := IntermediateField.adjoin.finiteDimensional
      ((Algebra.IsAlgebraic.isAlgebraic x).isIntegral)
    let : Algebra V E := ((algebraMap F E).comp V.subtype).toAlgebra
    let : IsScalarTower V F E := IsScalarTower.of_algebraMap_eq' rfl
    let : IsScalarTower V E K := IsScalarTower.of_algebraMap_eq fun a => by
      rw [IsScalarTower.algebraMap_apply V F K]
      rw [IsScalarTower.algebraMap_apply V F E]
      rw [IsScalarTower.algebraMap_apply F E K]
    let W' := W.comap (algebraMap E K)
    have hW' : W'.comap (algebraMap F E) = V := by
      rw [ValuationSubring.comap_comap, ← IsScalarTower.algebraMap_eq F E K]
      exact hW
    let x' : E := ⟨x, IntermediateField.mem_adjoin_simple_self F x⟩
    have hx' : x' ∈ W' := hx
    obtain ⟨a, s, hs, heq⟩ := (mem_extension_iff_fraction V W' hW' x').mp hx'
    let a' : integralClosure V K := ⟨algebraMap E K (a : E), a.property.algebraMap⟩
    let s' : integralClosure V K := ⟨algebraMap E K (s : E), s.property.algebraMap⟩
    refine ⟨a', s', ?_, ?_⟩
    · rw [mem_prolongationCenter, W.mem_nonunits_iff_or]
      rw [mem_prolongationCenter, W'.mem_nonunits_iff_or] at hs
      change ¬ ((s : E) = 0 ∨ algebraMap E K (s : E)⁻¹ ∉ W) at hs
      simpa only [s', map_eq_zero, ← map_inv₀] using hs
    · exact congrArg (algebraMap E K) heq |>.trans (map_div₀ _ _ _)
  · rintro ⟨a, s, hs, rfl⟩
    rw [mem_prolongationCenter, W.mem_nonunits_iff_or, not_or] at hs
    simpa only [div_eq_mul_inv] using W.mul_mem _ _
      (mem_of_isIntegral_of_comap_eq V W hW a.property) (not_not.mp hs.2)

end HereditaryAtomicity.ValuationAlgebra
