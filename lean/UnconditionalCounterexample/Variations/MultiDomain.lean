import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.RingTheory.Valuation.LocalSubring
import UnconditionalCounterexample.Variations.DimensionOne
import UnconditionalCounterexample.Variations.PointPullback
import UnconditionalCounterexample.Variations.MultivariateFibres
import UnconditionalCounterexample.IntersectionDomain

/-!
# The multivariate intersection and its reserved-point pullback

The polynomial sequence determines a localization inside the fraction field.
Intersecting with the ordinary valuation rings gives the first domain. The second domain imposes integrality of evaluation at the retained
rational point. The fraction field and integral closure are computed using
the canonical inclusions throughout.
-/

noncomputable section
namespace UnconditionalCounterexample.Variations.MultiDomain

open MvPolynomial IntersectionDomain WithZero
open scoped nonZeroDivisors

abbrev Polys (r : ℕ) := MvPolynomial (Fin r) ℚ

def coordinate {r : ℕ} (i : Fin r) : FunctionField r :=
  algebraMap (Polys r) (FunctionField r) (X i)

/-- The polynomial sequence and its ordinary places, in their common field. -/
structure Data (r : ℕ) where
  raw : ℕ → Polys r
  raw_ne : ∀ n, raw n ≠ 0
  primary : ℕ → Valuation (FunctionField r) ℤᵐ⁰
  guard : GuardSupport.PrimeIndex → Valuation (FunctionField r) ℤᵐ⁰

variable {r : ℕ} (A : Data r)

abbrev denominators := Submonoid.closure (Set.range A.raw)

theorem denominators_regular : denominators A ≤ (Polys r)⁰ := by
  apply Submonoid.closure_le.mpr
  rintro _ ⟨n, rfl⟩
  exact mem_nonZeroDivisors_iff_ne_zero.mpr (A.raw_ne n)

abbrev poleAlgebra := Localization.subalgebra.ofField (FunctionField r)
  (denominators A) (denominators_regular A)

def vertical : ℕ ⊕ GuardSupport.PrimeIndex → Valuation (FunctionField r) ℤᵐ⁰ :=
  Sum.elim A.primary A.guard

def ordinary : Subring (FunctionField r) := intersection (poleAlgebra A).toSubring (vertical A)

theorem mem_ordinary {z : FunctionField r} :
    z ∈ ordinary A ↔ z ∈ poleAlgebra A ∧ (∀ j, A.primary j z ≤ 1) ∧ ∀ p, A.guard p z ≤ 1 := by
  rw [ordinary, mem_intersection]
  exact and_congr_right fun _ ↦ ⟨fun h ↦ ⟨fun j ↦ h (.inl j), fun p ↦ h (.inr p)⟩,
    fun h i ↦ by cases i with | inl j => exact h.1 j | inr p => exact h.2 p⟩

theorem coordinate_mem (hp : ∀ j i, A.primary j (coordinate i) ≤ 1)
    (hg : ∀ p i, A.guard p (coordinate i) ≤ 1) (i : Fin r) : coordinate i ∈ ordinary A :=
  (mem_ordinary A).mpr ⟨(poleAlgebra A).algebraMap_mem _, fun j ↦ hp j i, fun p ↦ hg p i⟩

/-- A subring containing the coordinates generates the whole multivariate
fraction field, since its generated subfield already contains the rationals. -/
theorem fractionRing_of_coordinates (D : Subring (FunctionField r))
    (hD : ∀ i, coordinate i ∈ D) : IsFractionRing D (FunctionField r) := by
  let E := Subfield.closure (D : Set (FunctionField r))
  have hpoly (f : Polys r) : algebraMap (Polys r) (FunctionField r) f ∈ E := by
    induction f using MvPolynomial.induction_on with
    | C a =>
      rw [show C a = algebraMap ℚ (Polys r) a from rfl, ← IsScalarTower.algebraMap_apply]
      simp
    | add f g hf hg => simpa only [map_add] using E.add_mem hf hg
    | mul_X f i hf => simpa only [map_mul, coordinate] using E.mul_mem hf (Subfield.subset_closure (hD i))
  apply IsFractionRing.of_field
  intro z
  obtain ⟨x, y, _, hxy⟩ := IsFractionRing.div_surjective (Polys r) z
  have hz : z ∈ E := hxy ▸ E.div_mem (hpoly x) (hpoly y)
  obtain ⟨a, ha, b, hb, hab⟩ := Subfield.mem_closure_iff.mp hz
  rw [Subring.closure_eq] at ha hb
  exact ⟨⟨a,ha⟩, ⟨b,hb⟩, hab.symm⟩

theorem ordinary_fractionRing (hp : ∀ j i, A.primary j (coordinate i) ≤ 1)
    (hg : ∀ p i, A.guard p (coordinate i) ≤ 1) : IsFractionRing (ordinary A) (FunctionField r) :=
  fractionRing_of_coordinates _ (coordinate_mem A hp hg)

private theorem integral_mem_larger {K : Type*} [Field K] {D B : Subring K}
    (h : D ≤ B) [IsIntegrallyClosedIn B K] {x : K} (hx : IsIntegral D x) : x ∈ B :=
  Subring.isIntegrallyClosedIn_iff.mp inferInstance
    (IsIntegral.map_of_comp_eq (Subring.inclusion h) (RingHom.id K) rfl hx)

/-- Normality of the actual intersection of the horizontal localization and
all the ordinary valuation rings. -/
theorem ordinary_normal [IsFractionRing (ordinary A) (FunctionField r)] :
    IsIntegrallyClosed (ordinary A) := by
  let B := (poleAlgebra A).toSubring
  let : IsIntegrallyClosed (poleAlgebra A) :=
    isIntegrallyClosed_of_isLocalization _ _ (denominators_regular A)
  let : IsFractionRing B (FunctionField r) := inferInstanceAs (IsFractionRing (poleAlgebra A) _)
  let : IsIntegrallyClosedIn B (FunctionField r) :=
    (isIntegrallyClosed_iff_isIntegrallyClosedIn (FunctionField r)).mp
      (inferInstanceAs (IsIntegrallyClosed (poleAlgebra A)))
  apply Subring.isIntegrallyClosed_iff.mpr
  intro x hx
  apply (mem_intersection _ _ _).mpr
  refine ⟨integral_mem_larger (B := B) (intersection_le _ _) hx, fun i ↦ ?_⟩
  let V := (vertical A i).valuationSubring
  let : IsFractionRing V.toSubring (FunctionField r) := inferInstanceAs (IsFractionRing V _)
  let : IsIntegrallyClosedIn V.toSubring (FunctionField r) :=
    (isIntegrallyClosed_iff_isIntegrallyClosedIn (FunctionField r)).mp inferInstance
  have h : ordinary A ≤ V.toSubring := fun y hy ↦ ((mem_intersection _ _ _).mp hy).2 i
  exact integral_mem_larger h hx

variable (c : Fin r → ℚ) (hc : MultivariateFibres.Retained (denominators A) c)

def point : ordinary A →+* ℚ :=
  (MultivariateFibres.pointEval (denominators A) (poleAlgebra A) c hc).toRingHom.comp
    (inclusion (poleAlgebra A).toSubring (vertical A))

def pullback (q : ℕ) [Fact q.Prime] : Subring (FunctionField r) :=
  PointPullback.domain (ordinary A) (point A c hc) q

theorem pullback_fractionRing (q : ℕ) [Fact q.Prime] [IsFractionRing (ordinary A) (FunctionField r)] :
    IsFractionRing (pullback A c hc q) (FunctionField r) :=
  PointPullback.fractionRing _ _ _

theorem pullback_normal (q : ℕ) [Fact q.Prime] [IsFractionRing (ordinary A) (FunctionField r)] :
    IsIntegrallyClosed (pullback A c hc q) := by
  let := ordinary_normal A
  exact PointPullback.normal _ _ _

end UnconditionalCounterexample.Variations.MultiDomain
