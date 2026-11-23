import UnconditionalCounterexample.Hierarchy.WeightedPlace
import UnconditionalCounterexample.Hierarchy.PrescribedGuards
import UnconditionalCounterexample.PoleAlgebra

/-! # The polynomial pole ring with compact selected fibers and logarithmic guards -/

noncomputable section
namespace UnconditionalCounterexample.Hierarchy.Weighted

open Polynomial GuardSupport DiscreteOrders WithZero

local instance : Algebra ℚ (RatFunc ℚ) := RatFunc.instAlgebraOfPolynomial ℚ ℚ

abbrev Guard (P : ℕ → FiberPlace) :=
  {q : PrimeIndex // q ∉ Set.range (fun n => (P n).prime)}

abbrev Places (P : ℕ → FiberPlace) := (ℕ × Fiber) ⊕ Guard P

def placePrime (P : ℕ → FiberPlace) : Places P → PrimeIndex
  | .inl (n,_) => (P n).prime
  | .inr q => q.val

def valuation (P : ℕ → FiberPlace) : Places P → Valuation (RatFunc ℚ) ℤᵐ⁰
  | .inl (n,x) => EvaluationDVR.evaluationValuation _ ((P n).emb x).val ((P n).transcendental x)
  | .inr q => Prescribed.guardVal q.val

def ring (P : ℕ → FiberPlace) (S : Set ℚ[X]) : Subring (RatFunc ℚ) :=
  IntersectionDomain.intersection (PoleAlgebra.generated S).toSubring (valuation P)

theorem order_prime (P : ℕ → FiberPlace) (i : Places P) (q : PrimeIndex) :
    order (valuation P i) (q.val : RatFunc ℚ) = if placePrime P i = q then 1 else 0 := by
  have he (p : PrimeIndex) (e : RatFunc ℚ →+* ℚ_[p.val]) :
      order (EvaluationDVR.valuation p.val e) (q.val : RatFunc ℚ) = if p = q then 1 else 0 := by
    by_cases h : p = q
    · subst q
      simp [order]
    · simp [order, h, PairedSpectrum.valuation_other_prime p q e h]
  rcases i with ⟨n,x⟩ | q'
  · apply he
  · apply he

theorem order_polynomial (P : ℕ → FiberPlace) (n : ℕ) (x : Fiber) (f : ℚ[X]) :
    order (valuation P (.inl (n,x))) (algebraMap ℚ[X] (RatFunc ℚ) f) =
      (P n).polynomialOrder f x := by
  change -WithZero.log (Padic.mulValuation (LocalEvaluation.evalAt _ _
    (algebraMap ℚ[X] (RatFunc ℚ) f))) = _
  rw [LocalEvaluation.evalAt_apply, RatFunc.num_algebraMap, RatFunc.denom_algebraMap, map_one, div_one]
  change -WithZero.log (Padic.mulValuation (aeval ((P n).emb x).val f)) =
    (aeval ((P n).emb x).val f).valuation
  by_cases h : aeval ((P n).emb x).val f = (0 : ℚ_[(P n).prime.val])
  · simp [h]
  · simp [Padic.mulValuation,h]

end UnconditionalCounterexample.Hierarchy.Weighted
