import Factorization.Hereditary
import Factorization.OrderedGroup
import Mathlib.RingTheory.Valuation.Integers
import Mathlib.Algebra.Order.Group.Units

/-!
# Intrinsic units in a pulled-back valuation subring

The valuation convention is multiplicative: the subring consists of values at
most one. Inverting the values of its ambient-unit atoms gives positive elements
of the unit-value group, without any restriction on valuation rank.
-/

namespace HereditaryAtomicity

universe u v w

variable {R : Type u} {K : Type v} {Γ₀ : Type w}
  [CommRing R] [Field K] [LinearOrderedCommGroupWithZero Γ₀]

/-- The literal subring cut out by the pulled-back valuation. -/
def valuationSubring (f : R →+* K) (v : Valuation K Γ₀) : Subring R :=
  (v.comap f).integer

@[simp]
theorem mem_valuationSubring (f : R →+* K) (v : Valuation K Γ₀) (x : R) :
    x ∈ valuationSubring f v ↔ v (f x) ≤ 1 := Iff.rfl

/-- Valuation values of ambient units, as units of the valuation codomain. -/
def valuationUnitMap (f : R →+* K) (v : Valuation K Γ₀) : Rˣ →* Γ₀ˣ :=
  Units.map (v.toMonoidHom.comp f.toMonoidHom)

@[simp]
theorem coe_valuationUnitMap (f : R →+* K) (v : Valuation K Γ₀) (u : Rˣ) :
    (valuationUnitMap f v u : Γ₀) = v (f u) := rfl

/-- The actual subgroup of values attained by ambient units. -/
def valuationUnitSubgroup (f : R →+* K) (v : Valuation K Γ₀) : Subgroup Γ₀ˣ :=
  (valuationUnitMap f v).range

/-- A unit of the cut subring is an ambient unit of valuation one, and conversely. -/
theorem valuationSubring_isUnit_iff (f : R →+* K) (v : Valuation K Γ₀)
    (x : valuationSubring f v) :
    IsUnit x ↔ IsUnit (x : R) ∧ v (f x) = 1 := by
  constructor
  · intro hx
    refine ⟨hx.map (valuationSubring f v).subtype, ?_⟩
    exact Valuation.Integers.one_of_isUnit' (v := v.comap f)
      (O := valuationSubring f v) hx (fun y => y.property)
  · rintro ⟨⟨u, hu⟩, hv⟩
    have hvu : valuationUnitMap f v u = 1 := by
      apply Units.ext
      simpa only [coe_valuationUnitMap, hu, Units.val_one] using hv
    have hinv : (↑u⁻¹ : R) ∈ valuationSubring f v := by
      change (valuationUnitMap f v u⁻¹ : Γ₀) ≤ 1
      rw [map_inv, hvu]
      simp
    let xu : (valuationSubring f v)ˣ :=
      { val := x
        inv := ⟨↑u⁻¹, hinv⟩
        val_inv := by apply Subtype.ext; change (x : R) * ↑u⁻¹ = 1; rw [← hu]; simp
        inv_val := by apply Subtype.ext; change ↑u⁻¹ * (x : R) = 1; rw [← hu]; simp }
    exact xu.isUnit

/-- Intrinsic association in the cut subring preserves valuation because its
multiplying unit has valuation one. -/
theorem valuation_eq_of_associated (f : R →+* K) (v : Valuation K Γ₀)
    {x y : valuationSubring f v} (h : Associated x y) :
    v (f x) = v (f y) := by
  obtain ⟨u, hu⟩ := h
  have hvu := ((valuationSubring_isUnit_iff f v (u : valuationSubring f v)).mp
    u.isUnit).2
  have hh := congrArg (fun z : valuationSubring f v => v (f z)) hu
  simpa only [Subring.coe_mul, map_mul, hvu, mul_one] using hh

/-- Ambient-unit atoms in the cut subring have valuation strictly below one. -/
theorem valuation_lt_one_of_irreducible (f : R →+* K) (v : Valuation K Γ₀)
    {x : valuationSubring f v} (hx : Irreducible x) (hu : IsUnit (x : R)) :
    v (f x) < 1 := by
  apply lt_of_le_of_ne x.property
  intro hv
  exact hx.not_isUnit ((valuationSubring_isUnit_iff f v x).mpr ⟨hu, hv⟩)

/-- Every factor of a product associated to an ambient unit is an ambient unit.
The association and the factors are intrinsic to the actual cut subring. -/
theorem ambient_isUnit_of_mem_factorization (f : R →+* K) (v : Valuation K Γ₀)
    {x : valuationSubring f v} {s : Multiset (valuationSubring f v)}
    (hprod : Associated s.prod x) (hx : IsUnit (x : R))
    {a : valuationSubring f v} (ha : a ∈ s) : IsUnit (a : R) := by
  have h : IsUnit (s.prod : R) :=
    (hprod.map (valuationSubring f v).subtype.toMonoidHom).isUnit_iff.mpr hx
  exact isUnit_of_dvd_unit ((valuationSubring f v).subtype.map_dvd
    (Multiset.dvd_prod ha)) h

/-- An ambient-unit atom gives a positive indecomposable after inverting its
valuation. The subgroup is the actual image of all ambient units. -/
theorem atom_inverse_value_indecomposable (f : R →+* K) (v : Valuation K Γ₀)
    {x : valuationSubring f v} (hx : Irreducible x)
    (u : Rˣ) (hu : (u : R) = (x : R)) :
    Factorization.PositiveIndecomposable (valuationUnitSubgroup f v)
      (valuationUnitMap f v u)⁻¹ := by
  have hxu : IsUnit (x : R) := hu ▸ u.isUnit
  have hval : valuationUnitMap f v u < 1 := by
    change v (f u) < 1
    rw [hu]
    exact valuation_lt_one_of_irreducible f v hx hxu
  refine ⟨Subgroup.inv_mem _ (show valuationUnitMap f v u ∈ valuationUnitSubgroup f v from ⟨u, rfl⟩), one_lt_inv'.mpr hval, ?_⟩
  intro a b ha _ hb hc heq
  obtain ⟨r, hr⟩ := ha
  have hrval : valuationUnitMap f v r⁻¹ < 1 := by
    rw [map_inv, hr]
    exact inv_lt_one'.mpr hb
  have hprodval : valuationUnitMap f v (u * r) = b⁻¹ := by
    rw [map_mul, hr]
    have huval : valuationUnitMap f v u = (a * b)⁻¹ := by
      rw [← heq, inv_inv]
    rw [huval]
    simp [mul_comm]
  have hsval : valuationUnitMap f v (u * r) < 1 := by
    rw [hprodval]
    exact inv_lt_one'.mpr hc
  let rS : valuationSubring f v := ⟨↑r⁻¹, hrval.le⟩
  let sS : valuationSubring f v := ⟨↑(u * r), hsval.le⟩
  have hsplit : x = rS * sS := by
    apply Subtype.ext
    change (x : R) = ↑r⁻¹ * ↑(u * r)
    rw [← hu]
    simp [mul_comm]
  rcases hx.isUnit_or_isUnit hsplit with h | h
  · have hh := ((valuationSubring_isUnit_iff f v rS).mp h).2
    exact (ne_of_lt hrval) (Units.ext hh)
  · have hh := ((valuationSubring_isUnit_iff f v sS).mp h).2
    exact (ne_of_lt hsval) (Units.ext hh)

end HereditaryAtomicity
