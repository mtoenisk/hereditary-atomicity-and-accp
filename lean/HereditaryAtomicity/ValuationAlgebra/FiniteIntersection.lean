import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.Algebra.Field.GeomSum
import HereditaryAtomicity.ValuationAlgebra.GeometricDenominator
import Mathlib.Tactic.Ring

/-!
# Finite intersections of valuation subrings

A finite family admits simultaneous denominators which are units in any chosen
member containing the numerator. No rank or independence assumption is used.
-/

namespace HereditaryAtomicity.ValuationAlgebra.FiniteIntersection

open Finset

variable {L : Type*} [Field L]

private theorem inverse_mem_of_unit (W : ValuationSubring L) {x : W}
    (hx : IsUnit x) : (x : L)⁻¹ ∈ W := by
  obtain ⟨y, hxy⟩ := isUnit_iff_exists_inv.mp hx
  have hxy' : (x : L) * (y : L) = 1 := congrArg Subtype.val hxy
  have hx0 : (x : L) ≠ 0 := by
    intro h
    simp [h] at hxy'
  have hy : (y : L) = (x : L)⁻¹ := by
    apply (mul_left_cancel₀ hx0)
    rw [hxy', mul_inv_cancel₀ hx0]
  exact hy ▸ y.property

private theorem geometric_reverse (x : L) (hx : x ≠ 0) (n : ℕ) :
    (∑ j ∈ range (n + 1), x ^ j) * (x⁻¹) ^ n =
      ∑ j ∈ range (n + 1), (x⁻¹) ^ j := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, pow_succ (x⁻¹), add_mul]
    have hcancel : x ^ (n + 1) * ((x⁻¹) ^ n * x⁻¹) = 1 := by
      rw [← pow_succ, ← mul_pow, mul_inv_cancel₀ hx, one_pow]
    rw [hcancel, ← mul_assoc, ih]
    conv_rhs => rw [sum_range_succ']
    simp only [pow_succ, sum_mul, pow_zero]

private theorem geometric_unit_of_nonunit (W : ValuationSubring L) (y : W)
    (hy : y ∈ IsLocalRing.maximalIdeal W) (n : ℕ) :
    IsUnit (∑ j ∈ range (n + 1), y ^ j) := by
  rw [← IsLocalRing.residue_ne_zero_iff_isUnit]
  rw [RingHom.map_geom_sum, (IsLocalRing.residue_eq_zero_iff y).mpr hy]
  simp

private theorem reciprocal_geometric_mem (W : ValuationSubring L) {x : L}
    (hx : x ∉ W) (n : ℕ) :
    (∑ j ∈ range (n + 2), x ^ j)⁻¹ ∈ W ∧
      (∑ j ∈ range (n + 2), x ^ j)⁻¹ * x ∈ W := by
  have hx0 : x ≠ 0 := by intro h; exact hx (h ▸ W.zero_mem)
  have hyN : x⁻¹ ∈ W.nonunits := W.inv_mem_nonunits_iff.mpr (Or.inr hx)
  have hy : x⁻¹ ∈ W := W.nonunits_subset hyN
  let y : W := ⟨x⁻¹, hy⟩
  have hunit : IsUnit (∑ j ∈ range (n + 2), y ^ j) :=
    geometric_unit_of_nonunit W y (W.coe_mem_nonunits_iff.mp hyN) (n + 1)
  have hInv : (∑ j ∈ range (n + 2), (x⁻¹) ^ j)⁻¹ ∈ W := by
    have h := inverse_mem_of_unit W hunit
    change (W.subtype (∑ j ∈ range (n + 2), y ^ j))⁻¹ ∈ W at h
    simp only [map_sum, map_pow] at h
    exact h
  have hrev := geometric_reverse x hx0 (n + 1)
  have heq : (∑ j ∈ range (n + 2), x ^ j)⁻¹ =
      (x⁻¹) ^ (n + 1) * (∑ j ∈ range (n + 2), (x⁻¹) ^ j)⁻¹ := by
    rw [← hrev, mul_inv_rev, ← mul_assoc]
    simp [hx0]
  constructor
  · rw [heq]
    exact W.mul_mem _ _ (W.pow_mem hy _) hInv
  · rw [heq]
    have heq' : (x⁻¹) ^ (n + 1) * (∑ j ∈ range (n + 2), (x⁻¹) ^ j)⁻¹ * x =
        (x⁻¹) ^ n * (∑ j ∈ range (n + 2), (x⁻¹) ^ j)⁻¹ := by
      rw [pow_succ]
      calc
        _ = (x⁻¹) ^ n * (∑ j ∈ range (n + 2), (x⁻¹) ^ j)⁻¹ * (x⁻¹ * x) := by ring
        _ = _ := by rw [inv_mul_cancel₀ hx0, mul_one]
    rw [heq']
    exact W.mul_mem _ _ (W.pow_mem hy _) hInv

/-- An element of one member of a finite family admits a denominator integral
in every member and invertible in the chosen member. This is valid for arbitrary
valuation ranks and for families with repetitions or comparable members. -/
theorem exists_denominator {ι : Type*} [Finite ι] (W : ι → ValuationSubring L)
    (i : ι) {x : L} (hx : x ∈ W i) :
    ∃ s : L, s ≠ 0 ∧ (∀ j, s ∈ W j) ∧ (∀ j, s * x ∈ W j) ∧ s⁻¹ ∈ W i := by
  classical
  let J := {j : ι // x ∈ W j}
  obtain ⟨p, hp, hgood⟩ := HereditaryAtomicity.ValuationAlgebra.exists_prime_geomSum_ne_zero
    (fun j : J => IsLocalRing.ResidueField (W j.val))
    (fun j => IsLocalRing.residue (W j.val) ⟨x, j.property⟩)
  let d : L := ∑ k ∈ range p, x ^ k
  have hu (j : ι) (hj : x ∈ W j) :
      IsUnit (∑ k ∈ range p, (⟨x, hj⟩ : W j) ^ k) := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit, RingHom.map_geom_sum]
    exact hgood ⟨j, hj⟩
  have hd0 : d ≠ 0 := by
    have h := (hu i hx).map (W i).subtype
    have heq : (W i).subtype (∑ k ∈ range p, (⟨x, hx⟩ : W i) ^ k) = d := by
      simp only [map_sum, map_pow]
      rfl
    rw [heq] at h
    exact isUnit_iff_ne_zero.mp h
  have hm (j : ι) : d⁻¹ ∈ W j ∧ d⁻¹ * x ∈ W j := by
    by_cases hj : x ∈ W j
    · have h := inverse_mem_of_unit (W j) (hu j hj)
      change ((W j).subtype (∑ k ∈ range p, (⟨x, hj⟩ : W j) ^ k))⁻¹ ∈ W j at h
      simp only [map_sum, map_pow] at h
      have hd : d⁻¹ ∈ W j := h
      exact ⟨hd, (W j).mul_mem _ _ hd hj⟩
    · obtain ⟨n, hn⟩ := Nat.exists_eq_add_of_le hp.two_le
      have hp' : p = n + 2 := hn.trans (Nat.add_comm _ _)
      simpa only [d, hp'] using reciprocal_geometric_mem (W j) hj n
  refine ⟨d⁻¹, inv_ne_zero hd0, fun j => (hm j).1, fun j => (hm j).2, ?_⟩
  rw [inv_inv]
  exact (W i).toSubring.sum_mem fun k _ => (W i).pow_mem hx k

/-- The literal intersection of the embedded valuation subrings. -/
def intersection {ι : Type*} (W : ι → ValuationSubring L) : Subring L :=
  ⨅ j, (W j).toSubring

@[simp] theorem mem_intersection {ι : Type*} (W : ι → ValuationSubring L) (x : L) :
    x ∈ intersection W ↔ ∀ j, x ∈ W j := by
  simp [intersection]

theorem intersection_le {ι : Type*} (W : ι → ValuationSubring L) (i : ι) :
    intersection W ≤ (W i).toSubring := iInf_le _ i

/-- The actual center of one family member on their intersection. -/
def center {ι : Type*} (W : ι → ValuationSubring L) (i : ι) : Ideal (intersection W) :=
  Ideal.comap (Subring.inclusion (intersection_le W i) : intersection W →+* W i)
    (IsLocalRing.maximalIdeal (W i))

instance center_isPrime {ι : Type*} (W : ι → ValuationSubring L) (i : ι) :
    (center W i).IsPrime := by
  unfold center
  infer_instance

@[simp] theorem mem_center {ι : Type*} (W : ι → ValuationSubring L) (i : ι)
    (s : intersection W) : s ∈ center W i ↔ (s : L) ∈ (W i).nonunits :=
  (W i).coe_mem_nonunits_iff.symm

/-- Each family member is exactly the fractions in the intersection whose
denominators avoid its actual center. This is the localization representation,
with no assumed finiteness or rank restriction on the valuation rings. -/
theorem mem_iff_fraction {ι : Type*} [Finite ι] (W : ι → ValuationSubring L)
    (i : ι) (x : L) : x ∈ W i ↔
      ∃ a s : intersection W, s ∉ center W i ∧ x = (a : L) / (s : L) := by
  constructor
  · intro hx
    obtain ⟨s, hs0, hs, hsx, hsinv⟩ := exists_denominator W i hx
    refine ⟨⟨s * x, (mem_intersection W _).mpr hsx⟩,
      ⟨s, (mem_intersection W _).mpr hs⟩, ?_, ?_⟩
    · rw [mem_center, (W i).mem_nonunits_iff_or]
      exact not_or.mpr ⟨hs0, not_not.mpr hsinv⟩
    · exact (eq_div_iff hs0).mpr (mul_comm _ _)
  · rintro ⟨a, s, hs, rfl⟩
    rw [mem_center, (W i).mem_nonunits_iff_or, not_or] at hs
    simpa only [div_eq_mul_inv] using
      (W i).mul_mem _ _ (intersection_le W i a.property) (not_not.mp hs.2)

/-- The canonical inclusion identifies each member with the localization of the
intersection at its center, in mathlib's actual localization predicate. -/
theorem isLocalization {ι : Type*} [Finite ι] (W : ι → ValuationSubring L)
    (i : ι) :
    letI := (Subring.inclusion (intersection_le W i) : intersection W →+* W i).toAlgebra
    IsLocalization (center W i).primeCompl (W i) := by
  let := (Subring.inclusion (intersection_le W i) : intersection W →+* W i).toAlgebra
  apply (isLocalization_iff _ _).mpr
  refine ⟨?_, ?_, ?_⟩
  · intro s
    exact IsLocalRing.notMem_maximalIdeal.mp s.property
  · intro x
    obtain ⟨a, s, hs, heq⟩ := (mem_iff_fraction W i x).mp x.property
    have hs0 : (s : L) ≠ 0 := by
      intro h
      exact hs ((Subtype.ext h : s = 0).symm ▸ (center W i).zero_mem)
    refine ⟨⟨a, ⟨s, hs⟩⟩, ?_⟩
    exact Subtype.ext ((eq_div_iff hs0).mp heq)
  · intro x y h
    refine ⟨1, ?_⟩
    have hxy : x = y := Subtype.ext (congrArg (fun z : W i => (z : L)) h)
    rw [hxy]

/-- Centers determine the members of a finite family of valuation rings. -/
theorem eq_of_center_eq {ι : Type*} [Finite ι] (W : ι → ValuationSubring L)
    (i j : ι) (h : center W i = center W j) : W i = W j := by
  ext x
  rw [mem_iff_fraction W i, mem_iff_fraction W j, h]

end HereditaryAtomicity.ValuationAlgebra.FiniteIntersection
