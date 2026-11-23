import UnconditionalCounterexample.Hierarchy.EvaluationResidues
import UnconditionalCounterexample.Hierarchy.EvaluationClearing
import UnconditionalCounterexample.ReturnTargets
import UnconditionalCounterexample.Target

/-!
# A vertical localization is the restricted evaluation DVR

The evaluation ring is embedded in the common rational function field. A
polynomial cutoff at one fiber and a scalar unit at its rational prime give
a denominator outside the selected maximal ideal.
-/

noncomputable section
namespace UnconditionalCounterexample.Hierarchy

open Polynomial GuardSupport
variable (E : EvaluationFibers) (p : PrimeIndex) (a : E p)
variable (ha : Transcendental ℚ (a.val : ℚ_[p.val]))

private abbrev evalHom := EvaluationDVR.evaluationHom p.val (a.val : ℚ_[p.val]) ha
private abbrev evalDVR := (EvaluationDVR.valuation p.val (evalHom E p a ha)).valuationSubring

private theorem evalHom_poly (f : ℚ[X]) :
    evalHom E p a ha (algebraMap ℚ[X] (RatFunc ℚ) f) =
      f.eval₂ (Rat.castHom _) (a.val : ℚ_[p.val]) :=
  ReturnTargets.evaluationHom_polynomial p.val _ ha f

private def polyToDVR : evaluationPolynomials E →+* evalDVR E p a ha :=
  ((algebraMap ℚ[X] (RatFunc ℚ)).comp (evaluationPolynomials E).subtype).codRestrict
    (evalDVR E p a ha).toSubring (fun f => by
      apply (EvaluationDVR.mem_valuationSubring p.val _ _).mpr
      change ‖evalHom E p a ha (algebraMap ℚ[X] (RatFunc ℚ) f.val)‖ ≤ 1
      rw [evalHom_poly]
      exact (mem_evaluationPolynomials_iff E _).mp f.property p a.val a.property)

private theorem polyToDVR_isUnit (f : evaluationPolynomials E) (hf : f ∉ evaluationCenter E p a) :
    IsUnit (polyToDVR E p a ha f) := by
  by_contra h
  apply hf
  have hmem : polyToDVR E p a ha f ∈ IsLocalRing.maximalIdeal (evalDVR E p a ha) := h
  rw [← EvaluationDVR.residueMap_ker] at hmem
  change PadicInt.toZMod (integralEvaluation E p a f) = 0
  change PadicInt.toZMod (EvaluationDVR.integerMap p.val _ _) = 0 at hmem
  convert hmem using 2
  apply Subtype.ext
  exact (evalHom_poly E p a ha f.val).symm

private theorem exists_polynomial_repr (x : RatFunc ℚ) :
    ∃ f g : evaluationPolynomials E, algebraMap ℚ[X] (RatFunc ℚ) g.val ≠ 0 ∧
      x * algebraMap ℚ[X] (RatFunc ℚ) g.val = algebraMap ℚ[X] (RatFunc ℚ) f.val := by
  let := evaluationRing_fractionRing E
  obtain ⟨F, G, hG, heq⟩ := IsFractionRing.div_surjective (evaluationRing E) x
  obtain ⟨f,rfl⟩ := (evaluationRingEquiv E).surjective F
  obtain ⟨g,rfl⟩ := (evaluationRingEquiv E).surjective G
  have hn : algebraMap ℚ[X] (RatFunc ℚ) g.val ≠ 0 := fun h =>
    mem_nonZeroDivisors_iff_ne_zero.mp hG (Subtype.ext h)
  refine ⟨f,g,hn,?_⟩
  rw [← heq]
  exact div_mul_cancel₀ _ hn

/-- A cutoff corrects both polynomials on the selected fiber to integral values
and puts the denominator at a unit value at the chosen point. -/
def HasPairCutoff : Prop := ∀ f g : evaluationPolynomials E,
  integralEvaluation E p a g ≠ 0 →
  ‖integralEvaluation E p a f‖ ≤ ‖integralEvaluation E p a g‖ →
  ∃ H : ℚ[X], (∀ b : E p,
      ‖H.eval₂ (Rat.castHom _) (b.val : ℚ_[p.val]) * (integralEvaluation E p b f : ℚ_[p.val])‖ ≤ 1 ∧
      ‖H.eval₂ (Rat.castHom _) (b.val : ℚ_[p.val]) * (integralEvaluation E p b g : ℚ_[p.val])‖ ≤ 1) ∧
    ‖H.eval₂ (Rat.castHom _) (a.val : ℚ_[p.val]) * (integralEvaluation E p a g : ℚ_[p.val])‖ = 1

private theorem corrected_mem (d : ℕ) (H : ℚ[X])
    (haway : ∀ q : PrimeIndex, q ≠ p → ∀ b : ℤ_[q.val],
      ‖(d : ℚ_[q.val]) * H.eval₂ (Rat.castHom _) (b : ℚ_[q.val])‖ ≤ 1)
    (f : evaluationPolynomials E)
    (hloc : ∀ b : E p, ‖H.eval₂ (Rat.castHom _) (b.val : ℚ_[p.val]) *
        (integralEvaluation E p b f : ℚ_[p.val])‖ ≤ 1) :
    C (d : ℚ) * H * f.val ∈ evaluationPolynomials E := by
  apply (mem_evaluationPolynomials_iff E _).mpr
  intro q b hb
  rw [Polynomial.eval₂_mul, Polynomial.eval₂_mul, Polynomial.eval₂_C, map_natCast]
  by_cases hq : q = p
  · subst q
    rw [mul_assoc, norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (PadicInt.norm_le_one (d : ℤ_[p.val]))).trans (hloc ⟨b,hb⟩)
  · rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (haway q hq b)).trans
      ((mem_evaluationPolynomials_iff E _).mp f.property q b hb)

/-- At this evaluation center the localization is isomorphic to the specified
valuation subring of the rational function field. -/
def verticalStalkEquiv_of_cutoff (cut : HasPairCutoff E p a) :
    Localization.AtPrime (evaluationCenter E p a) ≃+*
      EvaluationDVR.evaluationRing p.val (a.val : ℚ_[p.val]) ha := by
  let φ := polyToDVR E p a ha
  let : Algebra (evaluationPolynomials E) (evalDVR E p a ha) := φ.toAlgebra
  let : IsLocalization (evaluationCenter E p a).primeCompl (evalDVR E p a ha) := by
    apply (isLocalization_iff _ _).mpr
    refine ⟨fun s => polyToDVR_isUnit E p a ha s.val s.property, ?_, ?_⟩
    · intro x
      obtain ⟨f,g,hg,hfg⟩ := exists_polynomial_repr E x.val
      have he := congrArg (evalHom E p a ha) hfg
      simp only [map_mul, evalHom_poly] at he
      have hgn : integralEvaluation E p a g ≠ 0 := by
        intro hz
        apply hg
        apply (evalHom E p a ha).injective
        rw [map_zero, evalHom_poly]
        exact congrArg (fun z : ℤ_[p.val] => (z : ℚ_[p.val])) hz
      have hx := (EvaluationDVR.mem_valuationSubring p.val (evalHom E p a ha) x.val).mp x.property
      have hbound : ‖integralEvaluation E p a f‖ ≤ ‖integralEvaluation E p a g‖ := by
        rw [PadicInt.norm_def, PadicInt.norm_def, integralEvaluation_coe, integralEvaluation_coe]
        rw [← he, norm_mul]
        exact mul_le_of_le_one_left (norm_nonneg _) hx
      obtain ⟨H,hH,hHu⟩ := cut f g hgn hbound
      obtain ⟨d,hd,haway⟩ := exists_away_clear p H
      let u : evaluationPolynomials E :=
        ⟨C (d : ℚ) * H * f.val, corrected_mem E p d H haway f (fun b => (hH b).1)⟩
      let s : evaluationPolynomials E :=
        ⟨C (d : ℚ) * H * g.val, corrected_mem E p d H haway g (fun b => (hH b).2)⟩
      have hs : s ∉ evaluationCenter E p a := by
        change PadicInt.toZMod (integralEvaluation E p a s) ≠ 0
        apply (padicInt_isUnit_iff_toZMod_ne_zero _).mp
        apply PadicInt.isUnit_iff.mpr
        change ‖(C (d : ℚ) * H * g.val).eval₂ (Rat.castHom _) (a.val : ℚ_[p.val])‖ = 1
        rw [Polynomial.eval₂_mul, Polynomial.eval₂_mul, Polynomial.eval₂_C, map_natCast, mul_assoc]
        rw [norm_mul, Padic.norm_natCast_eq_one_iff.mpr hd, one_mul]
        exact hHu
      refine ⟨⟨u, ⟨s, hs⟩⟩, ?_⟩
      apply Subtype.ext
      change x.val * algebraMap ℚ[X] (RatFunc ℚ) (C (d : ℚ) * H * g.val) =
        algebraMap ℚ[X] (RatFunc ℚ) (C (d : ℚ) * H * f.val)
      simp only [map_mul]
      rw [mul_left_comm, hfg]
    · intro f g h
      have he : f = g := by
        apply Subtype.ext
        apply RatFunc.algebraMap_injective ℚ
        exact congrArg (fun z : evalDVR E p a ha => (z : RatFunc ℚ)) h
      exact ⟨1, by rw [he]⟩
  exact (IsLocalization.algEquiv (evaluationCenter E p a).primeCompl
    (Localization.AtPrime (evaluationCenter E p a)) (evalDVR E p a ha)).toRingEquiv

end UnconditionalCounterexample.Hierarchy
