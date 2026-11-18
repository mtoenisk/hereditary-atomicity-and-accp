import Factorization.Definitions
import Mathlib.Algebra.Ring.Subring.Basic

/-!
# Intrinsic factorization under maps and equivalences

Multiplicative equivalences preserve irreducibility and units. Unit-reflecting
monoid maps pull back bounded nonunit factorizations, without injectivity.
For subrings, all factorization predicates use the subring's own units.
-/

namespace Factorization

universe u v

/-- Factorization bounds pull back along a homomorphism that reflects units. -/
theorem hasBoundedFactorizations_of_unitReflectingMap
    {R : Type u} {S : Type v} [CommMonoid R] [CommMonoid S]
    (f : R →* S) (hunit : ∀ r : R, IsUnit (f r) → IsUnit r)
    {x : R} (hx : HasBoundedFactorizations (f x)) : HasBoundedFactorizations x := by
  obtain ⟨bound, hb⟩ := hx
  refine ⟨bound, ?_⟩
  intro factors hn hf
  have hnon : ∀ p ∈ factors.map f, ¬ IsUnit p := by
    intro p hp
    obtain ⟨q, hq, rfl⟩ := Multiset.mem_map.mp hp
    exact fun hu => hn q hq (hunit q hu)
  have hassoc : Associated (factors.map f).prod (f x) := by
    rw [← map_multiset_prod]
    exact hf.map f
  simpa only [Multiset.card_map] using hb (factors.map f) hnon hassoc

/-- Bounded nonunit factorization lengths are invariant under an actual
multiplicative equivalence, using the intrinsic units on each side. -/
theorem hasBoundedFactorizations_mulEquiv_iff
    {R : Type u} {A : Type v} [CommMonoid R] [CommMonoid A]
    (e : R ≃* A) (x : R) :
    HasBoundedFactorizations (e x) ↔ HasBoundedFactorizations x := by
  constructor
  · exact hasBoundedFactorizations_of_unitReflectingMap e.toMonoidHom
      (fun y hy => (MulEquiv.isUnit_map e).mp hy)
  · intro hx
    apply hasBoundedFactorizations_of_unitReflectingMap e.symm.toMonoidHom
      (fun y hy => (MulEquiv.isUnit_map e.symm).mp hy)
    change HasBoundedFactorizations (e.symm (e x))
    simpa only [e.symm_apply_apply] using hx

/-- An actual multiplicative equivalence carries a finite irreducible
factorization to a finite irreducible factorization in the target ring. -/
theorem hasAtomicFactorization_map {R : Type u} {A : Type v}
    [CommMonoid R] [CommMonoid A] (e : R ≃* A)
    {x : R} (hx : HasAtomicFactorization x) : HasAtomicFactorization (e x) := by
  obtain ⟨s, hs, hx⟩ := hx
  refine ⟨s.map e.toMonoidHom, ?_, ?_⟩
  · intro y hy
    obtain ⟨z, hz, rfl⟩ := Multiset.mem_map.mp hy
    exact (MulEquiv.irreducible_iff e).mpr (hs z hz)
  · rw [← map_multiset_prod]
    exact hx.map e.toMonoidHom

/-- Atomic factorization is invariant under actual multiplicative equivalence. -/
theorem hasAtomicFactorization_mulEquiv_iff {R : Type u} {A : Type v}
    [CommMonoid R] [CommMonoid A] (e : R ≃* A) (x : R) :
    HasAtomicFactorization (e x) ↔ HasAtomicFactorization x := by
  constructor
  · intro hx
    simpa only [e.symm_apply_apply] using hasAtomicFactorization_map e.symm hx
  · exact hasAtomicFactorization_map e

/-- Intrinsic atomicity is invariant under an actual ring equivalence. -/
theorem isAtomicDomain_ringEquiv_iff {R : Type u} {A : Type v}
    [CommRing R] [IsDomain R] [CommRing A] [IsDomain A] (e : R ≃+* A) :
    IsAtomicDomain A ↔ IsAtomicDomain R := by
  constructor
  · intro h x hx
    apply (hasAtomicFactorization_mulEquiv_iff e.toMulEquiv x).mp
    apply h (e x)
    exact fun he => hx (e.injective (he.trans e.map_zero.symm))
  · intro h y hy
    obtain ⟨x, rfl⟩ := e.surjective y
    apply hasAtomicFactorization_map e.toMulEquiv
    apply h x
    exact fun hx => hy (hx ▸ e.map_zero)

/-- The image of an actual subring under an injective ring map has exactly the
same intrinsic atomicity as the original subring. -/
theorem subring_map_isAtomicDomain_iff {R : Type u} {A : Type v}
    [CommRing R] [IsDomain R] [CommRing A] [IsDomain A]
    (S : Subring R) (f : R →+* A) (hf : Function.Injective f) :
    IsAtomicDomain (S.map f) ↔ IsAtomicDomain S :=
  isAtomicDomain_ringEquiv_iff (S.equivMapOfInjective f hf)

/-- Bounded factorizations are invariant under an actual ring equivalence. -/
theorem isBFDomain_ringEquiv_iff {R : Type u} {A : Type v}
    [CommRing R] [IsDomain R] [CommRing A] [IsDomain A] (e : R ≃+* A) :
    IsBFDomain A ↔ IsBFDomain R := by
  constructor
  · intro h x hx
    apply (hasBoundedFactorizations_mulEquiv_iff e.toMulEquiv x).mp
    apply h (e x)
    exact fun he => hx (e.injective (he.trans e.map_zero.symm))
  · intro h y hy
    obtain ⟨x, rfl⟩ := e.surjective y
    apply (hasBoundedFactorizations_mulEquiv_iff e.toMulEquiv x).mpr
    apply h x
    exact fun hx => hy (hx ▸ e.map_zero)

/-- An injective ring map preserves the intrinsic BF property of its image subring. -/
theorem subring_map_isBFDomain_iff {R : Type u} {A : Type v}
    [CommRing R] [IsDomain R] [CommRing A] [IsDomain A]
    (S : Subring R) (f : R →+* A) (hf : Function.Injective f) :
    IsBFDomain (S.map f) ↔ IsBFDomain S :=
  isBFDomain_ringEquiv_iff (S.equivMapOfInjective f hf)

end Factorization
