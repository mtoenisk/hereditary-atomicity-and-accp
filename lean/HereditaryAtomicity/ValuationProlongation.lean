import Mathlib.RingTheory.Valuation.LocalSubring

/-!
# Prolongation along arbitrary field embeddings

A valuation subring extends along any field embedding. The proof uses domination
by a valuation ring, then reflects units to recover the exact original valuation.
No algebraicity, rank, finiteness, or extension-existence input is required.

Prolongations of valuations under field extension.
-/

namespace HereditaryAtomicity.ValuationProlongation

variable {K L : Type*} [Field K] [Field L]

/-- A local map from the base valuation into an upstairs valuation forces the
exact named restriction, rather than merely containment of the base ring. -/
theorem comap_eq_of_isLocalHom (f : K →+* L) (V : ValuationSubring K)
    (W : ValuationSubring L) (hmem : ∀ a : V, f a ∈ W)
    [IsLocalHom ((f.comp V.subtype).codRestrict W.toSubring hmem)] :
    W.comap f = V := by
  let g : V →+* W := (f.comp V.subtype).codRestrict W.toSubring hmem
  ext x
  constructor
  · intro hx
    by_contra hxV
    have hx0 : x ≠ 0 := fun he => hxV (he ▸ V.zero_mem)
    have hi : x⁻¹ ∈ V := (V.mem_or_inv_mem x).resolve_left hxV
    have hu : IsUnit (g ⟨x⁻¹, hi⟩) := by
      apply isUnit_iff_exists_inv.mpr
      refine ⟨⟨f x, hx⟩, ?_⟩
      apply Subtype.ext
      change f (x⁻¹) * f x = 1
      rw [← map_mul, inv_mul_cancel₀ hx0, map_one]
    have hv : IsUnit (⟨x⁻¹, hi⟩ : V) := IsUnit.of_map g _ hu
    obtain ⟨z, hz⟩ := isUnit_iff_exists_inv.mp hv
    have hzval : (z : K) = x := by
      have he : x⁻¹ * (z : K) = 1 := congrArg Subtype.val hz
      exact (inv_mul_eq_iff_eq_mul₀ hx0).mp he |>.trans (mul_one x)
    exact hxV (hzval ▸ z.property)
  · intro hx
    exact hmem ⟨x, hx⟩

/-- Every valuation subring has a prolongation along the specified field map. -/
theorem exists_prolongation (f : K →+* L) (V : ValuationSubring K) :
    ∃ W : ValuationSubring L, W.comap f = V := by
  obtain ⟨W, hW, hlocal⟩ := IsLocalRing.exists_factor_valuationRing (f.comp V.subtype)
  let : IsLocalHom ((f.comp V.subtype).codRestrict W.toSubring hW) := hlocal
  exact ⟨W, comap_eq_of_isLocalHom f V W hW⟩

/-- Restriction on the full spaces of valuation subrings is surjective. -/
theorem comap_surjective (f : K →+* L) :
    Function.Surjective (fun W : ValuationSubring L => W.comap f) :=
  exists_prolongation f

end HereditaryAtomicity.ValuationProlongation
