import Factorization.Hierarchy
import Factorization.Hereditary

/-!
# The hereditary factorization hierarchy

The domain hierarchy applies pointwise to every unital subring, using its own
units and irreducibles. All hypotheses remain explicit propositions.
-/

namespace Factorization

universe u

variable {R : Type u} [CommRing R] [IsDomain R]

/-- A hereditarily BF domain is hereditarily ACCP. -/
theorem IsHereditarilyBF.isHereditarilyACCP (hR : IsHereditarilyBF R) :
    IsHereditarilyACCP R :=
  fun S => (hR S).wfDvdMonoid

/-- A hereditarily ACCP domain is hereditarily atomic. -/
theorem IsHereditarilyACCP.isHereditarilyAtomic (hR : IsHereditarilyACCP R) :
    IsHereditarilyAtomic R :=
  fun S => isAtomicDomain_of_wfDvdMonoid (hR S)

/-- A hereditarily BF domain is hereditarily atomic. -/
theorem IsHereditarilyBF.isHereditarilyAtomic (hR : IsHereditarilyBF R) :
    IsHereditarilyAtomic R :=
  hR.isHereditarilyACCP.isHereditarilyAtomic

end Factorization
