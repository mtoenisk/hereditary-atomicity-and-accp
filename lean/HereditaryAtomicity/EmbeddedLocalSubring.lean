import HereditaryAtomicity.GeneratingSubringAtomicity
import Mathlib.RingTheory.LocalRing.RingHom.Basic

/-!
# Localization of an embedded subring at ambient units

The construction consists of actual fractions inside the ambient ring. When
the ambient ring is local it is the localization at the contracted maximal
ideal, with its numerator and unit-denominator presentation retained.
-/

noncomputable section
namespace HereditaryAtomicity

variable {R : Type*} [CommRing R]

/-- Fractions of elements of `C` whose denominators are units of `R`. -/
def embeddedLocalSubring (C : Subring R) : Subring R where
  carrier := {x | ∃ a b : C, IsUnit (b : R) ∧ x * (b : R) = (a : R)}
  zero_mem' := ⟨0, 1, isUnit_one, by simp⟩
  one_mem' := ⟨1, 1, isUnit_one, by simp⟩
  add_mem' := by
    rintro x y ⟨a, b, hb, hx⟩ ⟨c, d, hd, hy⟩
    refine ⟨a * d + c * b, b * d, hb.mul hd, ?_⟩
    change (x + y) * ((b : R) * d) = (a : R) * d + (c : R) * b
    calc
      (x + y) * ((b : R) * d) = (x * b) * d + (y * d) * b := by ring
      _ = (a : R) * d + (c : R) * b := by rw [hx, hy]
  mul_mem' := by
    rintro x y ⟨a, b, hb, hx⟩ ⟨c, d, hd, hy⟩
    refine ⟨a * c, b * d, hb.mul hd, ?_⟩
    change (x * y) * ((b : R) * d) = (a : R) * c
    calc
      (x * y) * ((b : R) * d) = (x * b) * (y * d) := by ring
      _ = (a : R) * c := by rw [hx, hy]
  neg_mem' := by
    rintro x ⟨a, b, hb, hx⟩
    refine ⟨-a, b, hb, ?_⟩
    change -x * (b : R) = -(a : R)
    rw [neg_mul, hx]

theorem le_embeddedLocalSubring (C : Subring R) : C ≤ embeddedLocalSubring C := by
  intro a ha
  exact ⟨⟨a, ha⟩, 1, isUnit_one, by simp⟩

theorem embeddedLocalSubring_denominator (C : Subring R) (x : embeddedLocalSubring C) :
    ∃ a b : C, IsUnit (b : R) ∧ (x : R) * (b : R) = (a : R) := x.property

/-- Ambient units are already units of this actual subring. -/
theorem embeddedLocalSubring_reflects_units (C : Subring R)
    (x : embeddedLocalSubring C) (hx : IsUnit (x : R)) : IsUnit x := by
  obtain ⟨a, b, hb, hxb⟩ := x.property
  have ha : IsUnit (a : R) := hxb ▸ hx.mul hb
  let y : R := (↑(hx.unit⁻¹) : R)
  have hy : y ∈ embeddedLocalSubring C := by
    refine ⟨b, a, ha, ?_⟩
    rw [← hxb, ← mul_assoc]
    have hyx : y * (x : R) = 1 := by
      dsimp [y]
      simpa only [IsUnit.unit_spec] using Units.inv_mul hx.unit
    rw [hyx, one_mul]
  apply isUnit_iff_exists_inv.mpr
  refine ⟨⟨y, hy⟩, Subtype.ext ?_⟩
  change (x : R) * y = 1
  dsimp [y]
  simpa only [IsUnit.unit_spec] using Units.mul_inv hx.unit

theorem embeddedLocalSubring_isUnit_iff (C : Subring R) (x : embeddedLocalSubring C) :
    IsUnit x ↔ IsUnit (x : R) :=
  ⟨fun h => h.map (embeddedLocalSubring C).subtype,
    embeddedLocalSubring_reflects_units C x⟩

instance embeddedLocalSubring_isLocalHom (C : Subring R) :
    IsLocalHom (embeddedLocalSubring C).subtype :=
  ⟨embeddedLocalSubring_reflects_units C⟩

instance embeddedLocalSubring_isLocalRing [IsLocalRing R] (C : Subring R) :
    IsLocalRing (embeddedLocalSubring C) :=
  (embeddedLocalSubring C).subtype.domain_isLocalRing

theorem embeddedLocalSubring_maximalIdeal [IsLocalRing R] (C : Subring R) :
    (IsLocalRing.maximalIdeal R).comap (embeddedLocalSubring C).subtype =
      IsLocalRing.maximalIdeal (embeddedLocalSubring C) :=
  IsLocalRing.maximalIdeal_comap _

/-- Its algebra structure is the literal inclusion of the original subring. -/
instance embeddedLocalSubring_algebra (C : Subring R) :
    Algebra C (embeddedLocalSubring C) :=
  (Subring.inclusion (le_embeddedLocalSubring C)).toAlgebra

theorem embeddedLocalSubring_isLocalization [IsLocalRing R] (C : Subring R) :
    IsLocalization ((IsLocalRing.maximalIdeal R).comap C.subtype).primeCompl
      (embeddedLocalSubring C) := by
  refine ⟨⟨?_, ?_, ?_⟩⟩
  · intro b
    apply embeddedLocalSubring_reflects_units
    change IsUnit (b.val : R)
    have hb : (b.val : R) ∉ IsLocalRing.maximalIdeal R := b.property
    simpa only [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not] using hb
  · intro x
    obtain ⟨a, b, hb, hx⟩ := x.property
    refine ⟨⟨a, ⟨b, ?_⟩⟩, Subtype.ext hx⟩
    change (b : R) ∉ IsLocalRing.maximalIdeal R
    simpa only [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not] using hb
  · intro a b h
    refine ⟨1, ?_⟩
    have hab : a = b := Subtype.ext (congrArg (fun z : embeddedLocalSubring C => (z : R)) h)
    change (1 : C) * a = (1 : C) * b
    simpa only [one_mul] using hab

end HereditaryAtomicity
