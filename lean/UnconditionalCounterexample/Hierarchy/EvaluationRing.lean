import UnconditionalCounterexample.GuardSupport
import UnconditionalCounterexample.RationalFunctionSubring

/-!
# Polynomial rings defined by integral evaluations on p-adic fibers

The fiber family gives a subring of the rational polynomial ring. Its image
under the canonical polynomial embedding is the corresponding subring of
the rational function field.
-/

noncomputable section
namespace UnconditionalCounterexample.Hierarchy

open Polynomial GuardSupport

abbrev EvaluationFibers := (p : PrimeIndex) → Set ℤ_[p.val]

/-- Rational polynomials taking integral values at the given p-adic points. -/
def evaluationPolynomials (E : EvaluationFibers) : Subring ℚ[X] :=
  ⨅ p : PrimeIndex, ⨅ a : E p, (PadicInt.subring p.val).comap
    (Polynomial.eval₂RingHom (Rat.castHom ℚ_[p.val]) (a.val : ℚ_[p.val]))

theorem mem_evaluationPolynomials_iff (E : EvaluationFibers) (f : ℚ[X]) :
    f ∈ evaluationPolynomials E ↔ ∀ p (a : ℤ_[p.val]), a ∈ E p →
      ‖f.eval₂ (Rat.castHom ℚ_[p.val]) (a : ℚ_[p.val])‖ ≤ 1 := by
  simp only [evaluationPolynomials, Subring.mem_iInf, Subtype.forall, Subring.mem_comap]
  rfl

/-- The same polynomial ring in its specified embedding in the function field. -/
def evaluationRing (E : EvaluationFibers) : Subring (RatFunc ℚ) :=
  (evaluationPolynomials E).map (algebraMap ℚ[X] (RatFunc ℚ))

theorem mem_evaluationRing_iff (E : EvaluationFibers) (x : RatFunc ℚ) :
    x ∈ evaluationRing E ↔ ∃ f : ℚ[X], algebraMap ℚ[X] (RatFunc ℚ) f = x ∧
      ∀ p (a : ℤ_[p.val]), a ∈ E p →
        ‖f.eval₂ (Rat.castHom ℚ_[p.val]) (a : ℚ_[p.val])‖ ≤ 1 := by
  simp only [evaluationRing, Subring.mem_map, mem_evaluationPolynomials_iff, and_comm]

def evaluationRingEquiv (E : EvaluationFibers) : evaluationPolynomials E ≃+* evaluationRing E :=
  (evaluationPolynomials E).equivMapOfInjective _ (RatFunc.algebraMap_injective ℚ)

theorem X_mem_evaluationPolynomials (E : EvaluationFibers) : X ∈ evaluationPolynomials E := by
  apply (mem_evaluationPolynomials_iff E _).mpr
  intro p a _
  simpa using a.property

theorem X_mem_evaluationRing (E : EvaluationFibers) : RatFunc.X ∈ evaluationRing E :=
  ⟨X, X_mem_evaluationPolynomials E, RatFunc.algebraMap_X⟩

theorem evaluationRing_fractionRing (E : EvaluationFibers) : IsFractionRing (evaluationRing E) (RatFunc ℚ) :=
  RationalFunctionSubring.isFractionRing_of_X_mem _ (X_mem_evaluationRing E)

/-- Evaluation as a map into the actual p-adic integers. -/
def integralEvaluation (E : EvaluationFibers) (p : PrimeIndex) (a : E p) :
    evaluationPolynomials E →+* ℤ_[p.val] :=
  ((Polynomial.eval₂RingHom (Rat.castHom ℚ_[p.val]) (a.val : ℚ_[p.val])).comp
    (evaluationPolynomials E).subtype).codRestrict (PadicInt.subring p.val)
    (fun f => (mem_evaluationPolynomials_iff E f.val).mp f.property p a.val a.property)

@[simp] theorem integralEvaluation_coe (E : EvaluationFibers) (p : PrimeIndex) (a : E p)
    (f : evaluationPolynomials E) : ((integralEvaluation E p a f : ℤ_[p.val]) : ℚ_[p.val]) =
    f.val.eval₂ (Rat.castHom ℚ_[p.val]) (a.val : ℚ_[p.val]) := rfl

def evaluationCenter (E : EvaluationFibers) (p : PrimeIndex) (a : E p) : Ideal (evaluationPolynomials E) :=
  RingHom.ker (PadicInt.toZMod.comp (integralEvaluation E p a))

instance (E : EvaluationFibers) (p : PrimeIndex) (a : E p) : (evaluationCenter E p a).IsPrime :=
  RingHom.ker_isPrime _

end UnconditionalCounterexample.Hierarchy
