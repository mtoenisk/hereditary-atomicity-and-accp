import UnconditionalCounterexample.Hierarchy.EvaluationRing
import UnconditionalCounterexample.EvaluationChoices
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.LocallyConstant.Algebra

/-!
# Residues over a rational prime

An element vanishes on a whole residue fiber exactly when it belongs to pA.
Compactness and Fermat's theorem then show that every maximal ideal above p
comes from one point of that fiber.
-/

noncomputable section
namespace UnconditionalCounterexample.Hierarchy

open Polynomial GuardSupport Filter
open scoped Topology BigOperators

variable (E : EvaluationFibers) (p : PrimeIndex)

abbrev pointResidue (a : E p) : evaluationPolynomials E →+* ZMod p.val :=
  PadicInt.toZMod.comp (integralEvaluation E p a)

theorem isLocallyConstant_pointResidue (f : evaluationPolynomials E) :
    IsLocallyConstant (fun a : E p => pointResidue E p a f) := by
  apply (IsLocallyConstant.iff_eventually_eq _).mpr
  intro a
  have hc : Continuous (fun b : E p => f.val.eval₂ (Rat.castHom ℚ_[p.val]) (b.val : ℚ_[p.val])) :=
    (f.val.continuous_eval₂ _).comp (continuous_subtype_val.comp continuous_subtype_val)
  have hnear := (Metric.tendsto_nhds.mp (hc.continuousAt (x := a))) 1 zero_lt_one
  filter_upwards [hnear] with b hb
  apply EvaluationChoices.toZMod_eq_of_norm_sub_lt_one
  exact hb

/-- Fiberwise evaluation modulo the rational prime. -/
def residueFunction : evaluationPolynomials E →+* LocallyConstant (E p) (ZMod p.val) where
  toFun f := ⟨_, isLocallyConstant_pointResidue E p f⟩
  map_zero' := by ext a; exact map_zero (pointResidue E p a)
  map_one' := by ext a; exact map_one (pointResidue E p a)
  map_add' f g := by ext a; exact map_add (pointResidue E p a) f g
  map_mul' f g := by ext a; exact map_mul (pointResidue E p a) f g

@[simp] theorem residueFunction_apply (f : evaluationPolynomials E) (a : E p) :
    residueFunction E p f a = pointResidue E p a f := rfl

theorem mem_span_prime_iff (f : evaluationPolynomials E) :
    f ∈ Ideal.span {(p.val : evaluationPolynomials E)} ↔ ∀ a : E p, pointResidue E p a f = 0 := by
  constructor
  · rintro hf a
    obtain ⟨g, hg⟩ := Ideal.mem_span_singleton.mp hf
    rw [hg, map_mul, map_natCast, ZMod.natCast_self, zero_mul]
  · intro hf
    let G : ℚ[X] := C (p.val : ℚ)⁻¹ * f.val
    have hG : G ∈ evaluationPolynomials E := by
      apply (mem_evaluationPolynomials_iff E _).mpr
      intro q a ha
      change ‖(C (p.val : ℚ)⁻¹ * f.val).eval₂ _ _‖ ≤ 1
      rw [Polynomial.eval₂_mul, Polynomial.eval₂_C, map_inv₀, map_natCast]
      by_cases hqp : q = p
      · subst q
        have hz : integralEvaluation E p ⟨a, ha⟩ f ∈ RingHom.ker PadicInt.toZMod := hf ⟨a, ha⟩
        rw [PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton] at hz
        obtain ⟨b, hb⟩ := hz
        have he := congrArg (fun z : ℤ_[p.val] => (z : ℚ_[p.val])) hb
        simp only [integralEvaluation_coe, PadicInt.coe_mul, PadicInt.coe_natCast] at he
        have hp : (p.val : ℚ_[p.val]) ≠ 0 := Nat.cast_ne_zero.mpr p.property.ne_zero
        change ‖(p.val : ℚ_[p.val])⁻¹ * f.val.eval₂ _ (a : ℚ_[p.val])‖ ≤ 1
        rw [show f.val.eval₂ _ (a : ℚ_[p.val]) = _ from he, inv_mul_cancel_left₀ hp]
        exact b.property
      · have hu : ‖(p.val : ℚ_[q.val])‖ = 1 :=
          Padic.norm_natCast_eq_one_iff.mpr ((Nat.coprime_primes q.property p.property).mpr
            (fun h => hqp (Subtype.ext h)))
        rw [norm_mul, norm_inv, hu, inv_one, one_mul]
        exact (mem_evaluationPolynomials_iff E _).mp f.property q a ha
    apply Ideal.mem_span_singleton.mpr
    refine ⟨⟨G,hG⟩, Subtype.ext ?_⟩
    have hp : (p.val : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr p.property.ne_zero
    change f.val = (p.val : ℚ[X]) * (C (p.val : ℚ)⁻¹ * f.val)
    rw [← Polynomial.C_eq_natCast, ← mul_assoc, ← map_mul, mul_inv_cancel₀ hp, map_one, one_mul]

theorem ker_residueFunction : RingHom.ker (residueFunction E p) =
    Ideal.span {(p.val : evaluationPolynomials E)} := by
  ext f
  rw [RingHom.mem_ker, mem_span_prime_iff]
  exact ⟨fun h a => congrArg (fun g : LocallyConstant (E p) (ZMod p.val) => g a) h,
    fun h => LocallyConstant.ext h⟩

/-- The compactness argument also applies to fibers with nonisolated points. -/
theorem exists_center_of_prime_mem (hc : IsCompact (E p))
    (M : Ideal (evaluationPolynomials E)) [hM : M.IsMaximal] (hp : (p.val : evaluationPolynomials E) ∈ M) :
    ∃ a : E p, M = evaluationCenter E p a := by
  classical
  let : CompactSpace (E p) := isCompact_iff_compactSpace.mp hc
  let Z (f : M) : Set (E p) := {a | pointResidue E p a f.val = 0}
  have hclosed (f : M) : IsClosed (Z f) :=
    (isLocallyConstant_pointResidue E p f.val).isClopen_fiber 0 |>.isClosed
  have hfin (s : Finset M) : (Set.univ ∩ ⋂ f ∈ s, Z f).Nonempty := by
    by_contra h
    have hout (a : E p) : ∃ f ∈ s, pointResidue E p a f.val ≠ 0 := by
      by_contra! hn
      exact h ⟨a, Set.mem_univ a, Set.mem_iInter₂.mpr hn⟩
    let u := ∏ f ∈ s, (1 - f.val ^ (p.val-1))
    have hu : u ∈ Ideal.span {(p.val : evaluationPolynomials E)} := by
      apply (mem_span_prime_iff E p u).mpr
      intro a
      obtain ⟨f,hf,hn⟩ := hout a
      dsimp only [u]
      rw [map_prod]
      apply Finset.prod_eq_zero hf
      simp only [map_sub, map_one, map_pow, ZMod.pow_card_sub_one_eq_one hn, sub_self]
    have hquot : Ideal.Quotient.mk M u = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr ((Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hp)) hu)
    have hone : Ideal.Quotient.mk M u = 1 := by
      dsimp only [u]
      rw [map_prod]
      apply Finset.prod_eq_one
      intro f _
      have hz := Ideal.Quotient.eq_zero_iff_mem.mpr f.property
      have hpos : p.val - 1 ≠ 0 := by have := p.property.one_lt; omega
      simp only [map_sub, map_one, map_pow, hz, zero_pow hpos, sub_zero]
    exact one_ne_zero (hone.symm.trans hquot)
  obtain ⟨a, _, ha⟩ := isCompact_univ.inter_iInter_nonempty Z hclosed hfin
  refine ⟨a, hM.eq_of_le (inferInstance : (evaluationCenter E p a).IsPrime).ne_top ?_⟩
  intro f hf
  exact Set.mem_iInter.mp ha ⟨f,hf⟩

end UnconditionalCounterexample.Hierarchy
