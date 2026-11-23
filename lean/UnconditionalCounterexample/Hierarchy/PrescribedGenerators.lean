import UnconditionalCounterexample.Hierarchy.PrescribedDomain
import UnconditionalCounterexample.Hierarchy.PrescribedSlices

/-! # Polynomial generators for the first slices of the prescribed rows -/

namespace UnconditionalCounterexample.Hierarchy.Prescribed

open Polynomial GuardSupport DiscreteOrders

/-- The last slice in each row is obtained by dividing the rational prime by
the product of the polynomials at the remaining slots. -/
abbrev Slot (m : ℕ → ℕ) := (i : ℕ) × Fin (m i + 1)

/-- The irreducible polynomials and their values at all actual evaluations. -/
structure Generators (m : ℕ → ℕ) (p : PrimeIndex) where
  poly : Slot m → ℚ[X]
  irreducible : ∀ s, Irreducible (poly s)
  row_order : ∀ s x, order (rowVal m p x) (algebraMap ℚ[X] (RatFunc ℚ) (poly s)) =
    (sliceAt s.1 s.2.castSucc x : ℤ)
  guard_order : ∀ s q, q ≠ p → order (guardVal q) (algebraMap ℚ[X] (RatFunc ℚ) (poly s)) = 0

variable {m : ℕ → ℕ} {p : PrimeIndex}

abbrev Generators.poles (G : Generators m p) := Set.range G.poly
noncomputable abbrev Generators.domain (G : Generators m p) := ring m p G.poles

end UnconditionalCounterexample.Hierarchy.Prescribed
