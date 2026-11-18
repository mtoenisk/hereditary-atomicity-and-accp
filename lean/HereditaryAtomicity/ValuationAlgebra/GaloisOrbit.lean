import HereditaryAtomicity.ValuationAlgebra.ExtensionFiber
import HereditaryAtomicity.ValuationProlongation
import HereditaryAtomicity.ValuationAlgebra.FiniteIntersection
import Mathlib.RingTheory.Invariant.Galois
import Mathlib.RingTheory.Localization.Integral

/-!
# Galois conjugates and the integral closure of a valuation ring

The integral closure is related to the actual named field restriction. All
conjugates are taken in the literal finite Galois group, without a choice of
common value group.
-/

namespace HereditaryAtomicity.ValuationAlgebra

open HereditaryAtomicity.ValuationProlongation

open Polynomial

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- An element integral over a base valuation belongs to every prolongation. -/
theorem mem_of_isIntegral_of_comap_eq (V : ValuationSubring K)
    [Algebra V L] [IsScalarTower V K L]
    (W : ValuationSubring L) (hW : W.comap (algebraMap K L) = V)
    {x : L} (hx : IsIntegral V x) : x ∈ W := by
  let g : V →+* W := (algebraMap V L).codRestrict W.toSubring (by
    intro a
    rw [IsScalarTower.algebraMap_apply V K L]
    change (a : K) ∈ W.comap (algebraMap K L)
    rw [hW]
    exact a.property)
  have heq : W.subtype.comp g = algebraMap V L := rfl
  have hx' : W.subtype.IsIntegralElem x := by
    apply RingHom.IsIntegralElem.of_comp (f := g)
    rwa [heq]
  obtain ⟨a, ha⟩ := (IsIntegrallyClosedIn.isIntegral_iff (R := W)).mp hx'
  exact ha ▸ a.property

/-- The actual inclusion of the integral closure into a prolongation. -/
def integralClosureToProlongation (V : ValuationSubring K)
    [Algebra V L] [IsScalarTower V K L]
    (W : ValuationSubring L) (hW : W.comap (algebraMap K L) = V) :
    integralClosure V L →+* W :=
  (integralClosure V L).toSubring.subtype.codRestrict W.toSubring
    (fun x => mem_of_isIntegral_of_comap_eq V W hW x.property)

/-- Center of a prolongation on the entire integral closure of the base valuation. -/
def prolongationCenter (V : ValuationSubring K)
    [Algebra V L] [IsScalarTower V K L]
    (W : ValuationSubring L) (hW : W.comap (algebraMap K L) = V) :
    Ideal (integralClosure V L) :=
  Ideal.comap (integralClosureToProlongation V W hW) (IsLocalRing.maximalIdeal W)

instance prolongationCenter_isPrime (V : ValuationSubring K)
    [Algebra V L] [IsScalarTower V K L]
    (W : ValuationSubring L) (hW : W.comap (algebraMap K L) = V) :
    (prolongationCenter V W hW).IsPrime := by
  unfold prolongationCenter
  infer_instance

@[simp] theorem mem_prolongationCenter (V : ValuationSubring K)
    [Algebra V L] [IsScalarTower V K L]
    (W : ValuationSubring L) (hW : W.comap (algebraMap K L) = V)
    (a : integralClosure V L) :
    a ∈ prolongationCenter V W hW ↔ (a : L) ∈ W.nonunits := by
  exact W.coe_mem_nonunits_iff.symm

/-- The center lies over exactly the original valuation's maximal ideal. -/
theorem prolongationCenter_under (V : ValuationSubring K)
    [Algebra V L] [IsScalarTower V K L]
    (W : ValuationSubring L) (hW : W.comap (algebraMap K L) = V) :
    (prolongationCenter V W hW).under V = IsLocalRing.maximalIdeal V := by
  ext a
  change algebraMap V (integralClosure V L) a ∈ prolongationCenter V W hW ↔ _
  rw [mem_prolongationCenter, ← V.coe_mem_nonunits_iff]
  change algebraMap V L a ∈ W.nonunits ↔ (a : K) ∈ V.nonunits
  rw [IsScalarTower.algebraMap_apply V K L, W.mem_nonunits_iff_or,
    V.mem_nonunits_iff_or, map_eq_zero, ← map_inv₀]
  change _ ∨ (a : K)⁻¹ ∉ W.comap (algebraMap K L) ↔ _
  rw [hW]
  rfl

/-- Restricting a prolongation along a base-field automorphism preserves its
named base restriction. -/
theorem comap_algEquiv_restrict (W : ValuationSubring L) (σ : L ≃ₐ[K] L) :
    (W.comap σ.toRingHom).comap (algebraMap K L) = W.comap (algebraMap K L) := by
  ext x
  change σ (algebraMap K L x) ∈ W ↔ algebraMap K L x ∈ W
  rw [σ.commutes]

/-- In a finite Galois extension, membership in every conjugate of one
prolongation detects integrality over the original valuation ring. -/
theorem isIntegral_iff_mem_all_conjugates [FiniteDimensional K L] [IsGalois K L]
    (V : ValuationSubring K) [Algebra V L] [IsScalarTower V K L]
    (W : ValuationSubring L) (hW : W.comap (algebraMap K L) = V) (x : L) :
    IsIntegral V x ↔ ∀ σ : L ≃ₐ[K] L, σ x ∈ W := by
  classical
  constructor
  · intro hx σ
    exact mem_of_isIntegral_of_comap_eq V W hW (hx.map σ)
  · intro hx
    let p : L[X] := MulSemiringAction.charpoly (L ≃ₐ[K] L) x
    have hpW : ∀ n, p.coeff n ∈ W := by
      let q : W[X] := ∏ σ : L ≃ₐ[K] L, (X - C ⟨σ x, hx σ⟩)
      have heq : q.map W.subtype = p := by
        simp [q, p, MulSemiringAction.charpoly, Polynomial.map_prod]
      intro n
      rw [← heq, Polynomial.coeff_map]
      exact (q.coeff n).property
    have hp : p ∈ Polynomial.lifts (algebraMap V L) := by
      rw [Polynomial.lifts_iff_coeff_lifts]
      intro n
      have hinv : p.coeff n ∈ IntermediateField.fixedField
          (⊤ : Subgroup (L ≃ₐ[K] L)) := by
        intro σ
        exact MulSemiringAction.smul_coeff_charpoly (G := L ≃ₐ[K] L) x n σ.val
      rw [IsGalois.fixedField_top, IntermediateField.mem_bot] at hinv
      obtain ⟨a, ha⟩ := hinv
      have haV : a ∈ V := by
        rw [← hW]
        change algebraMap K L a ∈ W
        rw [ha]
        exact hpW n
      refine ⟨⟨a, haV⟩, ?_⟩
      rw [IsScalarTower.algebraMap_apply V K L]
      exact ha
    obtain ⟨q, hq, -, hmonic⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hp
      (MulSemiringAction.monic_charpoly (L ≃ₐ[K] L) x)
    refine ⟨q, hmonic, ?_⟩
    rw [← Polynomial.eval_map, hq]
    exact MulSemiringAction.eval_charpoly (L ≃ₐ[K] L) x

/-- The entire integral closure equals the finite intersection of the actual
Galois conjugate valuation subrings. -/
theorem integralClosure_eq_iInf_conjugates [FiniteDimensional K L] [IsGalois K L]
    (V : ValuationSubring K) [Algebra V L] [IsScalarTower V K L]
    (W : ValuationSubring L) (hW : W.comap (algebraMap K L) = V) :
    (integralClosure V L).toSubring =
      ⨅ σ : L ≃ₐ[K] L, (W.comap σ.toRingHom).toSubring := by
  ext x
  rw [Subring.mem_iInf]
  change IsIntegral V x ↔ ∀ σ : L ≃ₐ[K] L, σ x ∈ W
  exact isIntegral_iff_mem_all_conjugates V W hW x

/-- The center on the entire integral closure determines a prolongation in a
finite Galois extension. The proof supplies common denominators in the finite
intersection of actual conjugate valuation rings. -/
theorem eq_of_prolongationCenter_eq [FiniteDimensional K L] [IsGalois K L]
    (V : ValuationSubring K) [Algebra V L] [IsScalarTower V K L]
    (W W' : ValuationSubring L)
    (hW : W.comap (algebraMap K L) = V)
    (hW' : W'.comap (algebraMap K L) = V)
    (hcenter : prolongationCenter V W hW = prolongationCenter V W' hW') : W = W' := by
  have hle (U U' : ValuationSubring L)
      (hU : U.comap (algebraMap K L) = V)
      (hU' : U'.comap (algebraMap K L) = V)
      (hc : prolongationCenter V U hU = prolongationCenter V U' hU') : U ≤ U' := by
    intro x hx
    have hx1 : x ∈ U.comap (1 : L ≃ₐ[K] L).toRingHom := hx
    obtain ⟨s, hs0, hs, hsx, hsi⟩ := FiniteIntersection.exists_denominator
      (fun σ : L ≃ₐ[K] L => U.comap σ.toRingHom) 1 hx1
    have hsI : IsIntegral V s :=
      (isIntegral_iff_mem_all_conjugates V U hU s).mpr hs
    have hsxI : IsIntegral V (s * x) :=
      (isIntegral_iff_mem_all_conjugates V U hU (s * x)).mpr hsx
    have hn : s ∉ U.nonunits := by
      rw [U.mem_nonunits_iff_or]
      exact not_or.mpr ⟨hs0, not_not.mpr hsi⟩
    have hn' : s ∉ U'.nonunits := by
      rw [← mem_prolongationCenter V U' hU' ⟨s, hsI⟩, ← hc,
        mem_prolongationCenter]
      exact hn
    have hsi' : s⁻¹ ∈ U' := by
      by_contra hi
      exact hn' (U'.mem_nonunits_iff_or.mpr (Or.inr hi))
    have hsx' : s * x ∈ U' := mem_of_isIntegral_of_comap_eq V U' hU' hsxI
    simpa only [← mul_assoc, inv_mul_cancel₀ hs0, one_mul] using
      U'.mul_mem _ _ hsi' hsx'
  exact le_antisymm (hle W W' hW hW' hcenter) (hle W' W hW' hW hcenter.symm)

omit [Algebra K L] in
@[simp] theorem mem_nonunits_comap (W : ValuationSubring L) (f : K →+* L) (x : K) :
    x ∈ (W.comap f).nonunits ↔ f x ∈ W.nonunits := by
  rw [(W.comap f).mem_nonunits_iff_or, W.mem_nonunits_iff_or, map_eq_zero,
    ← map_inv₀]
  rfl

open scoped Pointwise

/-- Prime-ideal transitivity on the actual integral closure gives conjugacy of
its valuation centers. Recovering the entire valuation ring from the center is
the separate localization step. -/
theorem exists_conjugate_center [FiniteDimensional K L] [IsGalois K L]
    (V : ValuationSubring K) [Algebra V L] [IsScalarTower V K L]
    (W W' : ValuationSubring L)
    (hW : W.comap (algebraMap K L) = V)
    (hW' : W'.comap (algebraMap K L) = V) :
    ∃ σ : L ≃ₐ[K] L, ∀ a : L, IsIntegral V a →
      (a ∈ W'.nonunits ↔ σ a ∈ W.nonunits) := by
  let B := integralClosure V L
  let : IsFractionRing B L := integralClosure.isFractionRing_of_finite_extension K L
  let := IsIntegralClosure.MulSemiringAction V K L B
  let : SMulCommClass (L ≃ₐ[K] L) V B :=
    ⟨fun σ a b => (galRestrict V K L B σ).toLinearEquiv.map_smul a b⟩
  let : Algebra.IsInvariant V B (L ≃ₐ[K] L) :=
    Algebra.isInvariant_of_isGalois V K L B
  obtain ⟨σ, hσ⟩ := Algebra.IsInvariant.exists_smul_of_under_eq V B (L ≃ₐ[K] L)
    (prolongationCenter V W hW) (prolongationCenter V W' hW')
    ((prolongationCenter_under V W hW).trans (prolongationCenter_under V W' hW').symm)
  refine ⟨σ⁻¹, fun a ha => ?_⟩
  let b : B := ⟨a, ha⟩
  change (b : L) ∈ W'.nonunits ↔ (σ⁻¹) (b : L) ∈ W.nonunits
  rw [← mem_prolongationCenter V W' hW' b, hσ,
    Ideal.mem_pointwise_smul_iff_inv_smul_mem, mem_prolongationCenter]
  have heq : ((σ⁻¹ • b : B) : L) = (σ⁻¹) (b : L) :=
    algebraMap_galRestrict_apply V (σ⁻¹) b
  rw [heq]

/-- The actual fibers of restriction in a finite Galois extension are Galois
orbits. No orbit-transitivity or extension-existence input is assumed. -/
theorem exists_comap_eq_of_comap_eq [FiniteDimensional K L] [IsGalois K L]
    (W W' : ValuationSubring L)
    (h : W.comap (algebraMap K L) = W'.comap (algebraMap K L)) :
    ∃ σ : L ≃ₐ[K] L, W.comap σ.toRingHom = W' := by
  let V := W.comap (algebraMap K L)
  let : Algebra V L := ((algebraMap K L).comp V.subtype).toAlgebra
  let : IsScalarTower V K L := IsScalarTower.of_algebraMap_eq' rfl
  have hW : W.comap (algebraMap K L) = V := rfl
  have hW' : W'.comap (algebraMap K L) = V := h.symm
  obtain ⟨σ, hσ⟩ := exists_conjugate_center V W W' hW hW'
  have hr : (W.comap σ.toRingHom).comap (algebraMap K L) = V :=
    (comap_algEquiv_restrict W σ).trans hW
  refine ⟨σ, eq_of_prolongationCenter_eq V (W.comap σ.toRingHom) W' hr hW' ?_⟩
  ext a
  rw [mem_prolongationCenter, mem_prolongationCenter, mem_nonunits_comap]
  exact (hσ a a.property).symm

/-- An entire restriction fiber is the set of the actual conjugates of any
one of its members. -/
theorem extensionFiber_eq_range_comap [FiniteDimensional K L] [IsGalois K L]
    (W : ValuationSubring L) :
    extensionFiber (algebraMap K L) (W.comap (algebraMap K L)) =
      Set.range (fun σ : L ≃ₐ[K] L => W.comap σ.toRingHom) := by
  ext W'
  constructor
  · intro hW'
    exact exists_comap_eq_of_comap_eq W W' hW'.symm
  · rintro ⟨σ, rfl⟩
    exact comap_algEquiv_restrict W σ

end HereditaryAtomicity.ValuationAlgebra
