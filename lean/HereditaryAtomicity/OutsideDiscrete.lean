import HereditaryAtomicity.JacobsonUnits
import Mathlib.RingTheory.Valuation.Discrete.Basic

/-!
# Outside rank-one valuations of Jacobson hereditary atomic domains

Simultaneous realization by units identifies the value group with the subgroup of
values of ambient units. Its positive generator gives discreteness of the outside
valuation ring.
-/

namespace HereditaryAtomicity

universe u v w

variable {R : Type u} {K : Type v} {Γ₀ : Type w}
  [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
  [LinearOrderedCommGroupWithZero Γ₀]

/-- The whole value group equals the actual ambient-unit image at an outside
rank-one valuation when the source has a nonzero Jacobson element. -/
theorem valueGroup_eq_valuationUnitSubgroup
    (v : Valuation K Γ₀) [v.RankOne] {j : R}
    (hj : j ∈ Ideal.jacobson (⊥ : Ideal R)) (hj0 : j ≠ 0)
    (hout : ∃ d : R, 1 < v (algebraMap R K d)) :
    MonoidWithZeroHom.valueGroup (.ofClass v) =
      valuationUnitSubgroup (algebraMap R K) v := by
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
    obtain ⟨u, hu⟩ := exists_unit_same_valuation v hj hj0 hout x hx0
    exact ⟨u, Units.ext (hu.trans hx)⟩
  · rintro ⟨u, rfl⟩
    exact (MonoidWithZeroHom.ofClass v).mem_valueGroup ⟨algebraMap R K u, rfl⟩

/-- An outside rank-one valuation of a hereditarily atomic domain with nonzero
Jacobson radical has an actual discrete valuation ring as its valuation subring. -/
theorem outside_isDiscreteValuationRing
    (hR : Factorization.IsHereditarilyAtomic R)
    (v : Valuation K Γ₀) [v.RankOne] {j : R}
    (hj : j ∈ Ideal.jacobson (⊥ : Ideal R)) (hj0 : j ≠ 0)
    (hout : ∃ d : R, 1 < v (algebraMap R K d)) :
    IsDiscreteValuationRing v.valuationSubring := by
  have hgroup := valueGroup_eq_valuationUnitSubgroup v hj hj0 hout
  let : IsCyclic (MonoidWithZeroHom.valueGroup (.ofClass v)) := by
    rw [hgroup]
    rcases valuationUnitSubgroup_eq_bot_or_eq_zpowers hR (algebraMap R K) v with h | ⟨g, _, h⟩
    · rw [h]
      infer_instance
    · rw [h]
      infer_instance
  exact Valuation.valuationSubring_isDiscreteValuationRing v

/-- The same conclusion for a literal outside valuation subring. -/
theorem outside_valuationSubring_isDiscreteValuationRing
    (hR : Factorization.IsHereditarilyAtomic R)
    (V : ValuationSubring K) [V.valuation.RankOne] {j : R}
    (hj : j ∈ Ideal.jacobson (⊥ : Ideal R)) (hj0 : j ≠ 0)
    (hout : ∃ d : R, algebraMap R K d ∉ V) : IsDiscreteValuationRing V := by
  have hout' : ∃ d : R, 1 < V.valuation (algebraMap R K d) := by
    obtain ⟨d, hd⟩ := hout
    exact ⟨d, lt_of_not_ge (fun h => hd ((V.valuation_le_one_iff _).mp h))⟩
  have h := outside_isDiscreteValuationRing hR V.valuation hj hj0 hout'
  change IsDiscreteValuationRing V.valuation.integer at h
  rw [V.integer_valuation] at h
  exact h

end HereditaryAtomicity
