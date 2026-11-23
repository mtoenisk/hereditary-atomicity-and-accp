import UnconditionalCounterexample.Variations.MultiDomain
import UnconditionalCounterexample.Variations.IndependentTuples

/-!
# Integral tuples as places of the multivariate domain

The primary evaluation takes values in the base p-adic field. A guard
evaluation can take values in its own finite unramified extension. Both are
implemented by evaluating the rational function at an independent tuple and
pulling its local valuation back to the common function field.
-/

noncomputable section
namespace UnconditionalCounterexample.Variations.MultiDomain

open GuardSupport WithZero

structure LocalTuple (r : ℕ) {L : Type*} [Field L] [Algebra ℚ L] (v : Valuation L ℤᵐ⁰) where
  x : Fin r → L
  independent : AlgebraicIndependent ℚ x
  integral : ∀ i, v (x i) ≤ 1

variable {r : ℕ} {L : Type*} [Field L] [Algebra ℚ L] {v : Valuation L ℤᵐ⁰}

namespace LocalTuple

def valuation (t : LocalTuple r v) : Valuation (FunctionField r) ℤᵐ⁰ :=
  v.comap (IndependentTuples.evaluation t.x t.independent)

@[simp] theorem valuation_coordinate (t : LocalTuple r v) (i : Fin r) :
    t.valuation (coordinate i) = v (t.x i) :=
  congrArg v (IndependentTuples.evaluation_variable t.x t.independent i)

@[simp] theorem valuation_natCast (t : LocalTuple r v) (n : ℕ) :
    t.valuation (n : FunctionField r) = v (n : L) := by simp [valuation]

end LocalTuple

/-- Each primary is rational p-adic. Each guard is evaluated in the field
assigned to its prime. Its normalized valuation sees that prime to order one. -/
structure Places (r : ℕ) where
  primes : ℕ → PrimeIndex
  injective : Function.Injective primes
  primary : (j : ℕ) → LocalTuple r (Padic.mulValuation (p := (primes j).val))
  guardField : PrimeIndex → Type
  [field : ∀ p, Field (guardField p)]
  [algebra : ∀ p, Algebra ℚ (guardField p)]
  guardVal : (p : PrimeIndex) → Valuation (guardField p) ℤᵐ⁰
  guard_prime : ∀ p, guardVal p (p.val : guardField p) = exp (-1)
  guard : (p : PrimeIndex) → LocalTuple r (guardVal p)

attribute [instance] Places.field Places.algebra

namespace Places

variable (P : Places r) (F : ℕ → Polys r) (hF : ∀ n, F n ≠ 0)

def data : Data r := ⟨F, hF, fun j ↦ (P.primary j).valuation, fun p ↦ (P.guard p).valuation⟩

theorem primary_prime (j : ℕ) : (P.data F hF).primary j ((P.primes j).val : FunctionField r) =
    exp (-1) :=
  EvaluationDVR.valuation_prime (P.primes j).val
    (IndependentTuples.evaluation (P.primary j).x (P.primary j).independent)

theorem data_guard_prime (p : PrimeIndex) : (P.data F hF).guard p (p.val : FunctionField r) = exp (-1) :=
  ((P.guard p).valuation_natCast _).trans (P.guard_prime p)

theorem ordinary_fraction : IsFractionRing (ordinary (P.data F hF)) (FunctionField r) :=
  ordinary_fractionRing _ (fun j i ↦ ((P.primary j).valuation_coordinate i).trans_le ((P.primary j).integral i))
    (fun p i ↦ ((P.guard p).valuation_coordinate i).trans_le ((P.guard p).integral i))

theorem ordinary_integrallyClosed : IsIntegrallyClosed (ordinary (P.data F hF)) := by
  let := P.ordinary_fraction F hF
  exact ordinary_normal _

end Places
end UnconditionalCounterexample.Variations.MultiDomain
