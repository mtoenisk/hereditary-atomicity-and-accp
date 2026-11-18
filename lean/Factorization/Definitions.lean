import Mathlib.RingTheory.UniqueFactorizationDomain.Defs
import Mathlib.Algebra.Ring.Defs

/-!
# Atomic and bounded factorizations

Element predicates use multisets and association in a commutative monoid.
They do not assume a chain condition, cancellation, or unique factorization.
Domain predicates exclude zero and include units via the empty factorization.
ACCP is mathlib's `WfDvdMonoid`; it is not part of the definition of atomicity.
-/

namespace Factorization

universe u

section Elements

variable {R : Type u} [CommMonoid R]

/-- A finite product of irreducibles, up to multiplication by a unit.
The empty multiset accounts for units. This assumes no chain condition. -/
def HasAtomicFactorization (x : R) : Prop :=
  ∃ factors : Multiset R,
    (∀ p ∈ factors, Irreducible p) ∧ Associated factors.prod x

/-- A bound for all factorizations into nonunits, without assuming atomicity. -/
def HasBoundedFactorizations (x : R) : Prop :=
  ∃ bound : ℕ, ∀ factors : Multiset R,
    (∀ p ∈ factors, ¬ IsUnit p) → Associated factors.prod x → factors.card ≤ bound

/-- Lengths of finite irreducible factorizations, with units absorbed by association.
Boundedness of this set alone does not assert existence of a factorization. -/
def factorizationLengths (x : R) : Set ℕ :=
  {n | ∃ factors : Multiset R,
    (∀ p ∈ factors, Irreducible p) ∧ Associated factors.prod x ∧ factors.card = n}

end Elements

/-- Atomicity for a domain, including unit elements via the empty factorization. -/
def IsAtomicDomain (R : Type u) [CommRing R] [IsDomain R] : Prop :=
  ∀ x : R, x ≠ 0 → HasAtomicFactorization x

/-- A nonzero element with bounded nonunit factorization lengths; units are allowed. -/
def IsBFElement {R : Type u} [CommRing R] (x : R) : Prop :=
  x ≠ 0 ∧ HasBoundedFactorizations x

/-- Every nonzero element has bounded nonunit factorizations.
The bound may depend on the element. -/
def IsBFDomain (R : Type u) [CommRing R] [IsDomain R] : Prop :=
  ∀ x : R, x ≠ 0 → HasBoundedFactorizations x

end Factorization
