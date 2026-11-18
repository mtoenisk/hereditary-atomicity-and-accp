import HereditaryAtomicity.CharP.LevelProfilesLattice
import HereditaryAtomicity.DVRBase.ValuationNorm

/-!
# Integer values on the actual DVR fraction field and its completion

Only the restriction to the coefficient fraction field is integer-valued.
No discreteness claim is made for the ambient algebraic extension.
-/

noncomputable section
namespace HereditaryAtomicity.DVRBase
open scoped NNReal

/-- Singleton-family form of the existing normalized DVR fraction-value theorem. -/
theorem normalized_base_fraction_order_integral
    (A k L : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field k] [Field L] [Algebra A k] [IsFractionRing A k]
    (f : k →+* L) (v : Valuation L ℝ≥0)
    (hv : ∀ a : A, v (f (algebraMap A k a)) ≤ 1)
    {π : A} (hπ : Irreducible π)
    (hnorm : realValuationOrder v (f (algebraMap A k π)) = 1)
    {x : k} (hx : x ≠ 0) : ∃ z : ℤ, realValuationOrder v (f x) = z := by
  obtain ⟨z, hz⟩ := normalized_dvr_fraction_orders A k L f
    (fun _ : Unit => v) (fun _ => hv) hπ (fun _ => hnorm) hx
  exact ⟨z, hz ()⟩

variable {K : Type*} [Field K]

/-- The canonical embedding of the fraction field of an actual coefficient subring. -/
def coefficientFractionEmbedding (A : Subring K) : FractionRing A →+* K :=
  IsFractionRing.lift (show Function.Injective A.subtype from Subtype.val_injective)

@[simp] theorem coefficientFractionEmbedding_algebraMap (A : Subring K) (a : A) :
    coefficientFractionEmbedding A (algebraMap A (FractionRing A) a) = (a : K) :=
  IsFractionRing.lift_algebraMap _ a

/-- The literal restriction of the ambient valuation to the coefficient fraction field. -/
def coefficientFractionValuation (A : Subring K) (v : Valuation K ℝ≥0) :
    Valuation (FractionRing A) ℝ≥0 := v.comap (coefficientFractionEmbedding A)

/-- The normalized coefficient fraction field has integer additive orders. -/
theorem coefficientFraction_order_integral (A : Subring K) [IsDiscreteValuationRing A]
    (v : Valuation K ℝ≥0) (hv : ∀ a : A, v (a : K) ≤ 1)
    {π : A} (hπ : Irreducible π) (hnorm : realValuationOrder v (π : K) = 1)
    {x : FractionRing A} (hx : x ≠ 0) :
    ∃ z : ℤ, realValuationOrder (coefficientFractionValuation A v) x = z := by
  exact normalized_base_fraction_order_integral A (FractionRing A) K
    (coefficientFractionEmbedding A) v (by simpa using hv) hπ
    (by simpa using hnorm) hx

/-- Completing the actual normalized coefficient fraction field preserves its
integer value group, without asserting integer values in the ambient field. -/
theorem coefficientCompletion_order_integral (A : Subring K) [IsDiscreteValuationRing A]
    (v : Valuation K ℝ≥0) (hv : ∀ a : A, v (a : K) ≤ 1)
    {π : A} (hπ : Irreducible π) (hnorm : realValuationOrder v (π : K) = 1)
    (x : ValuationNormCompletion (coefficientFractionValuation A v)) (hx : x ≠ 0) :
    ∃ z : ℤ, realValuationOrder (completionValuation (coefficientFractionValuation A v)) x = z := by
  exact completion_order_integral (coefficientFractionValuation A v)
    (fun a ha => coefficientFraction_order_integral A v hv hπ hnorm ha) x hx

end HereditaryAtomicity.DVRBase
