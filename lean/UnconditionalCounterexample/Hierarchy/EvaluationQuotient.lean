import UnconditionalCounterexample.Hierarchy.CompactApproximation
import UnconditionalCounterexample.Hierarchy.EvaluationResidues
import UnconditionalCounterexample.Hierarchy.EvaluationClearing

/-! # The residue-function quotient on a compact fibre -/

noncomputable section
namespace UnconditionalCounterexample.Hierarchy
open Polynomial GuardSupport

variable (E : EvaluationFibers) (p : PrimeIndex) (hc : IsCompact (E p))
include hc

/-- Every locally constant residue class on a compact fibre is represented by
a rational polynomial integral on every prescribed fibre. -/
theorem residueFunction_surjective : Function.Surjective (residueFunction E p) := by
  intro f
  let lift : LocallyConstant (E p) ℚ_[p.val] := f.map (fun y : ZMod p.val ↦ (y.val : ℚ_[p.val]))
  obtain ⟨P,hP⟩ := exists_polynomial_approx p (E p) hc lift (ε := 1) zero_lt_one
  let v (a : E p) := P.eval₂ (Rat.castHom ℚ_[p.val]) (a.val : ℚ_[p.val])
  have hn (a : E p) : ‖v a‖ ≤ 1 := by
    calc ‖v a‖ = ‖(v a - lift a) + lift a‖ := by rw [sub_add_cancel]
         _ ≤ max ‖v a - lift a‖ ‖lift a‖ := IsUltrametricDist.norm_add_le_max ..
         _ ≤ 1 := max_le (hP a).le (PadicInt.norm_le_one ((f a).val : ℤ_[p.val]))
  let u (a : E p) : ℤ_[p.val] := ⟨v a, hn a⟩
  have hu (a : E p) : PadicInt.toZMod (u a) = f a := by
    have h := EvaluationChoices.toZMod_eq_of_norm_sub_lt_one p.val
      (a := u a) (b := ((f a).val : ℤ_[p.val])) (by
        rw [PadicInt.norm_def,PadicInt.coe_sub,PadicInt.coe_natCast]
        exact hP a)
    simpa only [map_natCast,ZMod.natCast_zmod_val] using h
  obtain ⟨d, hd, hD⟩ := exists_away_clear p P
  let G := C (d : ℚ) * P
  have hG : G ∈ evaluationPolynomials E := by
    apply (mem_evaluationPolynomials_iff E G).mpr
    intro q a ha
    rw [show G = C (d : ℚ) * P from rfl,eval₂_mul,eval₂_C,map_natCast]
    by_cases hqp : q = p
    · subst q
      rw [norm_mul]
      exact (mul_le_of_le_one_left (norm_nonneg _) (PadicInt.norm_le_one (d : ℤ_[p.val]))).trans (hn ⟨a,ha⟩)
    · exact hD q hqp a
  let g : evaluationPolynomials E := ⟨G,hG⟩
  have hg (a : E p) : pointResidue E p a g = (d : ZMod p.val) * f a := by
    have he : integralEvaluation E p a g = (d : ℤ_[p.val]) * u a := by
      apply Subtype.ext
      rw [integralEvaluation_coe, PadicInt.coe_mul, PadicInt.coe_natCast]
      change (C (d : ℚ) * P).eval₂ (Rat.castHom ℚ_[p.val]) (a.val : ℚ_[p.val]) = (d : ℚ_[p.val]) * (u a : ℚ_[p.val])
      rw [eval₂_mul,eval₂_C,map_natCast]
    change PadicInt.toZMod (integralEvaluation E p a g) = _
    rw [he, map_mul, map_natCast, hu]
  let b := ((d : ZMod p.val)⁻¹).val
  have hd' : (d : ZMod p.val) ≠ 0 := ((ZMod.isUnit_iff_coprime _ _).mpr hd.symm).ne_zero
  refine ⟨(b : evaluationPolynomials E) * g, LocallyConstant.ext fun a ↦ ?_⟩
  change pointResidue E p a _ = f a
  rw [map_mul, map_natCast, hg, show (b : ZMod p.val) = _ from ZMod.natCast_zmod_val _,
    inv_mul_cancel_left₀ hd']

/-- The actual quotient of the integral-evaluation ring by the rational prime
is the ring of locally constant functions on its compact p-adic fibre. -/
def evaluationQuotientEquiv : (evaluationPolynomials E ⧸ Ideal.span {(p.val : evaluationPolynomials E)}) ≃+*
    LocallyConstant (E p) (ZMod p.val) :=
  (Ideal.quotEquivOfEq (ker_residueFunction E p).symm).trans
    (RingHom.quotientKerEquivOfSurjective (residueFunction_surjective E p hc))
end UnconditionalCounterexample.Hierarchy
