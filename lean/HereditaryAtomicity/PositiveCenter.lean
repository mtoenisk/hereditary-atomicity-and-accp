import Mathlib.RingTheory.Valuation.ValuationSubring

/-!
# Positive elements at a centered valuation

A nontrivial valuation containing a domain with the full ambient fraction field
has nonzero center. A positive fraction supplies a positive numerator.
-/

namespace HereditaryAtomicity

variable {K : Type*} [Field K]

/-- A nonzero positive fraction gives a nonzero positive source element at a
valuation containing the source. No dimension or rank hypothesis is needed. -/
theorem exists_nonzero_positive_of_centered (D : Subring K) [IsFractionRing D K]
    (V : ValuationSubring K) (hDV : D ≤ V.toSubring)
    (z : K) (hz0 : z ≠ 0) (hz : z ∈ V.nonunits) :
    ∃ h : K, h ≠ 0 ∧ h ∈ D ∧ h ∈ V.nonunits := by
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective D z
  have hb0 : (b : K) ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
  have ha0 : (a : K) ≠ 0 := by
    intro ha
    apply hz0
    rw [← hab]
    change (a : K) / (b : K) = 0
    rw [ha, zero_div]
  have haz : (a : K) = z * (b : K) := (div_eq_iff hb0).mp hab
  refine ⟨a, ha0, a.property, V.mem_nonunits_iff.mpr ?_⟩
  rw [haz, map_mul]
  have hbV : V.valuation (b : K) ≤ 1 :=
    (V.valuation_le_one_iff _).mpr (hDV b.property)
  calc
    V.valuation z * V.valuation (b : K) ≤ V.valuation z * 1 :=
      mul_le_mul_of_nonneg_left hbV zero_le
    _ = V.valuation z := mul_one _
    _ < 1 := V.mem_nonunits_iff.mp hz

end HereditaryAtomicity
