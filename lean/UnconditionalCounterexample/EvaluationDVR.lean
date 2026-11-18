import UnconditionalCounterexample.LocalEvaluation
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.RingTheory.Valuation.Discrete.Basic

/-!
# Rational p-adic evaluation DVRs

Restriction of the p-adic valuation along the given embedding gives a DVR with
uniformizer p and residue field ℤ/pℤ. Evaluation at a transcendental p-adic argument
supplies the vertical valuation rings of the construction.
-/

noncomputable section
namespace UnconditionalCounterexample.EvaluationDVR
open WithZero
variable (p : ℕ) [hp : Fact p.Prime]
variable {K : Type*} [Field K] (e : K →+* ℚ_[p])

/-- Restrict the normalized p-adic valuation along a field homomorphism. -/
def valuation : Valuation K ℤᵐ⁰ := (Padic.mulValuation (p := p)).comap e

/-- The rational prime has additive value one under the restricted valuation. -/
@[simp] theorem valuation_prime : valuation p e (p : K) = exp (-1) := by
  simp [valuation, Padic.mulValuation, hp.out.ne_zero]

/-- The prime witnesses that the restricted valuation is nontrivial. -/
instance valuation_nontrivial : (valuation p e).IsNontrivial := by
  exact ⟨p, by simp, by simp⟩

/-- The restricted integer-valued valuation has cyclic value group. -/
theorem valueGroup_isCyclic : IsCyclic (MonoidWithZeroHom.valueGroup (.ofClass (valuation p e))) := by
  infer_instance

/-- Restricting the valuation retains rank-one discreteness. -/
theorem valuation_isRankOneDiscrete : (valuation p e).IsRankOneDiscrete := by infer_instance

/-- The restricted valuation ring is a DVR. -/
theorem valuationSubring_isDVR : IsDiscreteValuationRing (valuation p e).valuationSubring := by
  infer_instance

/-- The rational prime itself is a uniformizer in the restricted field. -/
theorem prime_isUniformizer : (valuation p e).IsUniformizer (p : K) := by
  rw [Valuation.IsUniformizer.iff,
    Valuation.IsRankOneDiscrete.generator_eq_exp_neg_one_of_mem_range]
  · simp
  · exact ⟨p, valuation_prime p e⟩

/-- Membership is exactly p-adic integrality after evaluation. -/
theorem mem_valuationSubring (x : K) :
    x ∈ (valuation p e).valuationSubring ↔ ‖e x‖ ≤ 1 := by
  rw [Valuation.mem_valuationSubring_iff]
  change Padic.mulValuation (e x) ≤ 1 ↔ ‖e x‖ ≤ 1
  simpa only [norm_one, map_one, not_lt] using
    (not_congr (Padic.norm_lt_norm_iff_mulValuation_lt (x := 1) (y := e x))).symm

/-- Evaluation maps the restricted valuation ring into the p-adic integers. -/
def integerMap : (valuation p e).valuationSubring →+* ℤ_[p] :=
  (e.comp (valuation p e).valuationSubring.subtype).codRestrict (PadicInt.subring p)
    fun x => (mem_valuationSubring p e x).mp x.property

/-- The restricted residue map is evaluation followed by reduction modulo `p`. -/
def residueMap : (valuation p e).valuationSubring →+* ZMod p :=
  PadicInt.toZMod.comp (integerMap p e)

/-- Integer constants already map onto every residue class. -/
theorem residueMap_surjective : Function.Surjective (residueMap p e) :=
  ZMod.ringHom_surjective _

/-- The kernel of reduction is the actual maximal ideal of the restricted DVR. -/
theorem residueMap_ker : RingHom.ker (residueMap p e) =
    IsLocalRing.maximalIdeal (valuation p e).valuationSubring := by
  ext x
  change integerMap p e x ∈ RingHom.ker PadicInt.toZMod ↔ _
  rw [PadicInt.ker_toZMod, IsLocalRing.mem_maximalIdeal,
    mem_nonunits_iff, PadicInt.not_isUnit_iff, Valuation.mem_maximalIdeal_iff]
  change ‖e x.val‖ < 1 ↔ Padic.mulValuation (e x.val) < 1
  simpa only [norm_one, map_one] using
    (Padic.norm_lt_norm_iff_mulValuation_lt (x := e x.val) (y := 1))

/-- The residue field of the restricted DVR is exactly the prime field. -/
def residueEquiv : IsLocalRing.ResidueField (valuation p e).valuationSubring ≃+* ZMod p :=
  (Ideal.quotEquivOfEq (residueMap_ker p e).symm).trans
    (RingHom.quotientKerEquivOfSurjective (residueMap_surjective p e))

variable (a : ℚ_[p]) (ha : Transcendental ℚ a)

/-- The evaluation embedding, retaining the polynomial-induced algebra structure on `ℚ(t)`. -/
def evaluationHom : RatFunc ℚ →+* ℚ_[p] :=
  @AlgHom.toRingHom ℚ (RatFunc ℚ) (ℚ_[p]) _ _ _ (RatFunc.instAlgebraOfPolynomial ℚ ℚ) _
    (LocalEvaluation.evalAt a ha)

/-- The rational-function variable evaluates to the chosen argument. -/
@[simp] theorem evaluationHom_X : evaluationHom p a ha RatFunc.X = a :=
  LocalEvaluation.evalAt_X a ha

/-- The p-adic valuation on `ℚ(t)` obtained by evaluation at `a`. -/
def evaluationValuation : Valuation (RatFunc ℚ) ℤᵐ⁰ :=
  valuation p (evaluationHom p a ha)

/-- The evaluation valuation is rank-one discrete. -/
instance evaluationValuation_isRankOneDiscrete : (evaluationValuation p a ha).IsRankOneDiscrete :=
  valuation_isRankOneDiscrete p _

/-- The actual p-adic evaluation DVR inside `ℚ(t)`. -/
abbrev evaluationRing := (evaluationValuation p a ha).valuationSubring

/-- The evaluation ring is a DVR without a completeness hypothesis on its fraction field. -/
instance evaluationRing_isDVR : IsDiscreteValuationRing (evaluationRing p a ha) :=
  valuationSubring_isDVR p _

/-- The canonical inclusion realizes `ℚ(t)` as the fraction field of its evaluation ring. -/
theorem evaluationRing_fractionRing :
    IsFractionRing (evaluationRing p a ha) (RatFunc ℚ) := by infer_instance

/-- The variable has the valuation of the chosen argument. -/
@[simp] theorem evaluationValuation_X :
    evaluationValuation p a ha RatFunc.X = Padic.mulValuation a := by
  simp [evaluationValuation, valuation]

/-- The prime is a uniformizer at every transcendental evaluation argument. -/
theorem evaluation_prime_isUniformizer :
    (evaluationValuation p a ha).IsUniformizer (p : RatFunc ℚ) :=
  prime_isUniformizer p _

/-- Evaluation-ring membership has the expected analytic meaning. -/
theorem mem_evaluationRing (f : RatFunc ℚ) :
    f ∈ evaluationRing p a ha ↔ ‖LocalEvaluation.evalAt a ha f‖ ≤ 1 :=
  mem_valuationSubring p _ f

/-- Every rational-function evaluation DVR has residue field `ZMod p`. -/
def evaluationResidueEquiv :
    IsLocalRing.ResidueField (evaluationRing p a ha) ≃+* ZMod p :=
  residueEquiv p _

end UnconditionalCounterexample.EvaluationDVR
