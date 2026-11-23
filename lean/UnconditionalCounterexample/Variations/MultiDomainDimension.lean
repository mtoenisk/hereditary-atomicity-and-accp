import UnconditionalCounterexample.Variations.MultiDomainLocalization
import UnconditionalCounterexample.Variations.DimensionFlags
import UnconditionalCounterexample.Variations.AffineDimension

/-!
# The retained flag in the multivariate domains

Integer localization contracts the flag through the retained rational point
to each domain. In the pullback, reduction at that point contains the top
of the flag and contains the reserved prime. Thus its dimension is exactly
one greater than the number of variables.
-/

noncomputable section
namespace UnconditionalCounterexample.Variations.MultiDomain

open MvPolynomial IntersectionDomain

variable {r : ℕ} {A : Data r} (c : Fin r → ℚ) (hc : MultivariateFibres.Retained (denominators A) c)
include hc

private theorem flag_top_disjoint :
    Disjoint ((denominators A) : Set (Polys r)) (coordinateFlag c r le_rfl).last.asIdeal := by
  change Disjoint _ ((coordinatePrime c r).asIdeal : Set (Polys r))
  rw [coordinatePrime_full]
  exact Set.disjoint_left.mpr fun f hf hzero ↦ hc ⟨f, hf⟩ hzero

def horizontalFlag : LTSeries (PrimeSpectrum (poleAlgebra A)) :=
  liftPrimeFlag _ (denominators A) (coordinateFlag c r le_rfl) (flag_top_disjoint c hc)

theorem horizontalFlag_top :
    (horizontalFlag c hc).last.asIdeal =
      RingHom.ker (MultivariateFibres.pointEval (denominators A) (poleAlgebra A) c hc).toRingHom := by
  have h := liftPrimeFlag_comap (poleAlgebra A) (denominators A) (coordinateFlag c r le_rfl)
    (flag_top_disjoint c hc) (Fin.last r)
  have he : (horizontalFlag c hc).last.asIdeal.under (Polys r) = (coordinatePrime c r).asIdeal :=
    congrArg PrimeSpectrum.asIdeal h
  rw [MultivariateFibres.pointEval_ker_eq_map, ← IsLocalization.map_under (denominators A)
    (poleAlgebra A) (horizontalFlag c hc).last.asIdeal, he, coordinatePrime_full]
  rfl

theorem ordinary_dimension_lower (H : Clearing A) : (r : WithBot ℕ∞) ≤ ringKrullDim (ordinary A) := by
  let := ordinary_integerLocalization H
  exact Order.LTSeries.length_le_krullDim
    (contractPrimeFlag (poleAlgebra A) (integerDenominators (ordinary A)) (horizontalFlag c hc))

theorem ordinary_dimension (H : Clearing A)
    (hvertical : ∀ v : PrimeSpectrum (ordinary A),
      ¬ Disjoint (integerDenominators (ordinary A) : Set (ordinary A)) v.asIdeal → Order.height v ≤ r) :
    ringKrullDim (ordinary A) = r := by
  let := ordinary_integerLocalization H
  refine le_antisymm (?_ : ringKrullDim (ordinary A) ≤ r) (ordinary_dimension_lower c hc H)
  exact ringKrullDim_le_of_vertical_heights (poleAlgebra A) (integerDenominators (ordinary A)) r
    (ringKrullDim_localization_at_retained_point c (denominators A) (poleAlgebra A) hc).le hvertical

/-- The reserved prime strictly extends the generic flag. Finite-type
contraction over the integers gives the opposite bound on the same ring. -/
theorem pullback_dimension (H : Clearing A) (q : ℕ) [Fact q.Prime] :
    ringKrullDim (pullback A c hc q) = (r+1 : ℕ) := by
  let D := pullback A c hc q
  let B := poleAlgebra A
  let W := PointPullback.localRationals q
  let f := (MultivariateFibres.pointEval (denominators A) B c hc).toRingHom.comp (algebraMap D B)
  have hint (x : D) : f x ∈ W := by
    obtain ⟨y, hy, he⟩ := x.property
    have hyx : (y : FunctionField r) = x := he
    have heq : algebraMap D B x = inclusion (poleAlgebra A).toSubring (vertical A) y :=
      Subtype.ext hyx.symm
    change MultivariateFibres.pointEval _ _ c hc (algebraMap D B x) ∈ W
    rw [heq]
    exact hy
  let reduction := (PointPullback.reduction q).comp (f.codRestrict W hint)
  let Q : PrimeSpectrum D := ⟨RingHom.ker reduction, RingHom.ker_isPrime _⟩
  let := pullback_integerLocalization H c hc q
  refine le_antisymm (rationalFunctionField_subring_dimension_le r D) ?_
  apply succ_length_le_of_vertical_prime B (integerDenominators D) (horizontalFlag c hc) Q
  · intro x hx
    have h : algebraMap D B x ∈ (horizontalFlag c hc).last.asIdeal := hx
    rw [horizontalFlag_top] at h
    have hw : (f.codRestrict W hint) x = 0 := Subtype.ext h
    change PointPullback.reduction q ((f.codRestrict W hint) x) = 0
    rw [hw, map_zero]
  · have hden : (q : D) ∈ integerDenominators D := by
      refine ⟨(q : ℤ), mem_nonZeroDivisors_iff_ne_zero.mpr ?_, by simp⟩
      exact_mod_cast (Fact.out : q.Prime).ne_zero
    exact ⟨⟨q,hden⟩, by change reduction (q : D) = 0; rw [map_natCast, ZMod.natCast_self]⟩

end UnconditionalCounterexample.Variations.MultiDomain
