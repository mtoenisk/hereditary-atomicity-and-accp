import HereditaryAtomicity.UnitValues
import Mathlib.RingTheory.Valuation.Discrete.Basic

/-!
# Valuation rings of hereditarily atomic fields

In a field every nonzero element is a unit. Hereditary atomicity thus restricts the
entire value group, and each proper valuation ring is a DVR.
-/

namespace HereditaryAtomicity

universe u v

variable {K : Type u} [Field K] {Γ₀ : Type v}
  [LinearOrderedCommGroupWithZero Γ₀]

/-- In a field, the full value group is exactly the image of its unit group. -/
theorem field_valueGroup_eq_valuationUnitSubgroup (v : Valuation K Γ₀) :
    MonoidWithZeroHom.valueGroup (.ofClass v) =
      valuationUnitSubgroup (RingHom.id K) v := by
  ext g
  constructor
  · intro hg
    have hmem : (g : Γ₀) ∈ Units.val '' MonoidWithZeroHom.valueGroup (.ofClass v) :=
      ⟨g, hg, rfl⟩
    rw [MonoidWithZeroHom.valueGroup_eq_range] at hmem
    obtain ⟨⟨x, hx⟩, _⟩ := hmem
    have hx0 : x ≠ 0 := by
      intro hx0
      rw [hx0, map_zero] at hx
      exact g.ne_zero hx.symm
    exact ⟨Units.mk0 x hx0, Units.ext hx⟩
  · rintro ⟨u, rfl⟩
    exact (MonoidWithZeroHom.ofClass v).mem_valueGroup ⟨(u : K), rfl⟩

/-- Every nontrivial valuation of an HA field has a DVR as its valuation ring. -/
theorem field_valuation_isDiscreteValuationRing
    (hK : Factorization.IsHereditarilyAtomic K)
    (v : Valuation K Γ₀) [v.IsNontrivial] :
    IsDiscreteValuationRing v.valuationSubring := by
  let : IsCyclic (MonoidWithZeroHom.valueGroup (.ofClass v)) := by
    rw [field_valueGroup_eq_valuationUnitSubgroup v]
    rcases valuationUnitSubgroup_eq_bot_or_eq_zpowers hK (RingHom.id K) v with
      h | ⟨g, _, h⟩
    · rw [h]
      infer_instance
    · rw [h]
      infer_instance
  exact Valuation.valuationSubring_isDiscreteValuationRing v

/-- Every proper literal valuation subring of an HA field is a DVR. -/
theorem field_valuationSubring_isDiscreteValuationRing
    (hK : Factorization.IsHereditarilyAtomic K)
    (V : ValuationSubring K) (hV : V ≠ ⊤) : IsDiscreteValuationRing V := by
  let : V.valuation.IsNontrivial := by
    by_contra hn
    exact hV (V.eq_top_iff.mpr hn)
  have h := field_valuation_isDiscreteValuationRing hK V.valuation
  change IsDiscreteValuationRing V.valuation.integer at h
  rw [V.integer_valuation] at h
  exact h

end HereditaryAtomicity
