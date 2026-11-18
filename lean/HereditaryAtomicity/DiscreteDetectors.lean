import Factorization.Bounds
import Mathlib.RingTheory.DiscreteValuationRing.Basic

/-!
# Natural factor-count measurements from discrete valuation rings

The value at zero is set to zero by `ENat.toNat`; additivity is asserted only
for nonzero factors. All nonunit detection statements retain that premise.
-/

namespace HereditaryAtomicity

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

/-- The finite order of a nonzero DVR element, extended by zero at zero. -/
noncomputable def discreteOrder (x : R) : ℕ :=
  (IsDiscreteValuationRing.addVal R x).toNat

theorem discreteOrder_eq_zero_of_isUnit {x : R} (hx : IsUnit x) :
    discreteOrder x = 0 := by
  simp [discreteOrder, IsDiscreteValuationRing.addVal_eq_zero_iff.mpr hx]

theorem discreteOrder_mul {x y : R} (hx : x ≠ 0) (hy : y ≠ 0) :
    discreteOrder (x * y) = discreteOrder x + discreteOrder y := by
  unfold discreteOrder
  rw [IsDiscreteValuationRing.addVal_mul]
  exact ENat.toNat_add (mt IsDiscreteValuationRing.addVal_eq_top_iff.mp hx)
    (mt IsDiscreteValuationRing.addVal_eq_top_iff.mp hy)

theorem discreteOrder_pos {x : R} (hx : x ≠ 0) (hnu : ¬ IsUnit x) :
    0 < discreteOrder x := by
  exact ENat.toNat_pos (mt IsDiscreteValuationRing.addVal_eq_zero_iff.mp hnu)
    (mt IsDiscreteValuationRing.addVal_eq_top_iff.mp hx)

/-- Every nonunit factor contributes at least one to the DVR order. -/
theorem factorization_card_le_discreteOrder {x : R} (hx : x ≠ 0)
    (t : Multiset R) (ht : ∀ a ∈ t, ¬ IsUnit a) (hprod : Associated t.prod x) :
    t.card ≤ discreteOrder x := by
  exact Factorization.factorization_card_le_natDegree discreteOrder
    (fun _ => discreteOrder_eq_zero_of_isUnit)
    (fun _ _ => discreteOrder_mul) hx
    (fun _ ha _ hnu => discreteOrder_pos ha hnu) t ht hprod

end HereditaryAtomicity
