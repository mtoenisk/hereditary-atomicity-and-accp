import Factorization

/-- In a hereditarily ACCP domain, a nonzero element of any subring factors
using the irreducibles of that subring. -/
example {R : Type*} [CommRing R] [IsDomain R]
    (hR : Factorization.IsHereditarilyACCP R) (S : Subring R) (x : S) (hx : x ≠ 0) :
    ∃ factors : Multiset S, (∀ p ∈ factors, Irreducible p) ∧ Associated factors.prod x :=
  hR.isHereditarilyAtomic S x hx
