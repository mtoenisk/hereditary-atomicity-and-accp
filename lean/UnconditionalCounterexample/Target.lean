import Factorization.Hereditary
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Localization.AtPrime.Basic

/-!
# Exact targets for the rational-function counterexample

These predicates describe subrings of RatFunc ℚ with hereditary atomicity, failure of
ACCP, and specified chains. Every subring uses its own units and irreducibles.
-/

namespace UnconditionalCounterexample

universe u

/-- A domain whose localizations at all maximal ideals are discrete valuation rings. -/
def IsAlmostDedekindDomain (R : Type u) [CommRing R] [IsDomain R] : Prop :=
  ∀ (M : Ideal R) [M.IsMaximal], IsDiscreteValuationRing (Localization.AtPrime M)

/-- A strict chain of actual principal ideals with a specified initial element. -/
def HasStrictChainAt {R : Type u} [CommRing R] (a : R) : Prop :=
  ∃ x : ℕ → R, x 0 = a ∧ (∀ n, x n ≠ 0) ∧
    StrictMono (fun n => Ideal.span ({x n} : Set R))

/-- The core source conclusion about the actual embedded domain.
The last conjunct locates the non-ACCP chain at the literal rational function `X^3`. -/
def CoreConclusion (D : Subring (RatFunc ℚ)) : Prop :=
  Factorization.IsHereditarilyAtomic D ∧
  ¬ WfDvdMonoid D ∧
  IsFractionRing D (RatFunc ℚ) ∧
  IsAlmostDedekindDomain D ∧
  ∃ a : D, (a : RatFunc ℚ) = RatFunc.X ^ 3 ∧ HasStrictChainAt a

/-- The unconditional core existence target. No inhabitant is asserted here. -/
def CounterexampleExists : Prop :=
  ∃ D : Subring (RatFunc ℚ), CoreConclusion D

end UnconditionalCounterexample
