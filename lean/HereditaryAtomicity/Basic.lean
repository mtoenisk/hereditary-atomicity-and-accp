import Factorization.Hereditary

/-!
# Basic hereditary atomicity for embedded subrings

This first client of the shared factorization library works with actual unital
subrings of an ambient domain. It separates mere containment in the ambient ring
from the intrinsic units and irreducibles used in the smaller ring. No semilocal
structure, valuation restriction, or localization theorem is assumed or proved here.
-/

namespace HereditaryAtomicity

open Factorization

universe u v

/-- An embedded domain in a hereditarily atomic domain is hereditarily atomic. -/
theorem of_injective {R : Type u} {A : Type v}
    [CommRing R] [IsDomain R] [CommRing A] [IsDomain A]
    (f : R →+* A) (hf : Function.Injective f) (hA : IsHereditarilyAtomic A) :
    IsHereditarilyAtomic R :=
  hA.of_injective f hf

/-- For two actual subrings of an ambient domain, hereditary atomicity of the
larger one gives hereditary atomicity of the smaller one. -/
theorem of_subring_le {K : Type u} [CommRing K] [IsDomain K]
    {S T : Subring K} (hST : S ≤ T) (hT : IsHereditarilyAtomic T) :
    IsHereditarilyAtomic S :=
  hT.of_injective (Subring.inclusion hST) (fun _ _ h => Subtype.ext (congrArg (fun z : T => (z : K)) h))

/-- Every nonzero element of the smaller embedded subring factors into its own
irreducibles, with an association by a unit of that smaller subring. -/
theorem factorization_of_subring_le {K : Type u} [CommRing K] [IsDomain K]
    {S T : Subring K} (hST : S ≤ T) (hT : IsHereditarilyAtomic T)
    (x : S) (hx : x ≠ 0) :
    ∃ factors : Multiset S,
      (∀ p ∈ factors, Irreducible p) ∧ Associated factors.prod x :=
  (of_subring_le hST hT).isAtomicDomain x hx

/-- An injective change of ambient coordinates preserves hereditary atomicity
of an actual subring in either direction. -/
theorem map_iff {R : Type u} {A : Type v}
    [CommRing R] [IsDomain R] [CommRing A] [IsDomain A]
    (S : Subring R) (f : R →+* A) (hf : Function.Injective f) :
    IsHereditarilyAtomic (S.map f) ↔ IsHereditarilyAtomic S :=
  isHereditarilyAtomic_ringEquiv_iff (S.equivMapOfInjective f hf)

end HereditaryAtomicity
