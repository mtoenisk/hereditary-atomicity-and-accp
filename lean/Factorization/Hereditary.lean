import Factorization.Transport
import Mathlib.Order.RelIso.Basic

/-!
# Hereditary factorization properties of domains

Every property here quantifies over all unital subrings, with units and
irreducibles computed in the subring itself. Transport along an injective ring
map uses its image subrings; it does not require the map to reflect ambient units.
ACCP uses mathlib's `WfDvdMonoid` rather than a separate chain-condition definition.
-/

namespace Factorization

universe u v

/-- Every unital subring is atomic, using its own units and irreducibles. -/
def IsHereditarilyAtomic (R : Type u) [CommRing R] [IsDomain R] : Prop :=
  ∀ S : Subring R, IsAtomicDomain S

/-- Every unital subring has bounded nonunit factorizations at each nonzero element. -/
def IsHereditarilyBF (R : Type u) [CommRing R] [IsDomain R] : Prop :=
  ∀ S : Subring R, IsBFDomain S

/-- Every unital subring satisfies ACCP, expressed by well-founded strict divisibility. -/
def IsHereditarilyACCP (R : Type u) [CommRing R] [IsDomain R] : Prop :=
  ∀ S : Subring R, WfDvdMonoid S

section Equivalence

variable {R : Type u} {A : Type v} [CommRing R] [CommRing A]

/-- A ring equivalence transports well-founded strict divisibility. -/
theorem wfDvdMonoid_of_ringEquiv (e : R ≃+* A) (h : WfDvdMonoid A) :
    WfDvdMonoid R := by
  apply RelHomClass.wellFounded
    (RelHom.mk (fun x : R => e x) ?_ : (DvdNotUnit : R → R → Prop) →r DvdNotUnit) h
  intro x y hxy
  obtain ⟨hx, a, ha, hya⟩ := hxy
  refine ⟨?_, e a, ?_, ?_⟩
  · exact fun hzero => hx (e.injective (hzero.trans e.map_zero.symm))
  · exact fun hu => ha ((MulEquiv.isUnit_map e).mp hu)
  · simpa only [map_mul] using congrArg e hya

/-- ACCP is invariant under ring equivalence. -/
theorem wfDvdMonoid_ringEquiv_iff (e : R ≃+* A) :
    WfDvdMonoid A ↔ WfDvdMonoid R :=
  ⟨wfDvdMonoid_of_ringEquiv e, wfDvdMonoid_of_ringEquiv e.symm⟩

/-- The image of a subring under an injective map has the same intrinsic ACCP. -/
theorem subring_map_wfDvdMonoid_iff (S : Subring R) (f : R →+* A)
    (hf : Function.Injective f) : WfDvdMonoid (S.map f) ↔ WfDvdMonoid S :=
  wfDvdMonoid_ringEquiv_iff (S.equivMapOfInjective f hf)

end Equivalence

section Domains

variable {R : Type u} {A : Type v}
  [CommRing R] [IsDomain R] [CommRing A] [IsDomain A]

/-- Hereditary atomicity pulls back through an injective ring map. -/
theorem IsHereditarilyAtomic.of_injective (hA : IsHereditarilyAtomic A)
    (f : R →+* A) (hf : Function.Injective f) : IsHereditarilyAtomic R := by
  intro S
  exact (subring_map_isAtomicDomain_iff S f hf).mp (hA (S.map f))

/-- Hereditary bounded factorization pulls back through an injective ring map. -/
theorem IsHereditarilyBF.of_injective (hA : IsHereditarilyBF A)
    (f : R →+* A) (hf : Function.Injective f) : IsHereditarilyBF R := by
  intro S
  exact (subring_map_isBFDomain_iff S f hf).mp (hA (S.map f))

/-- Hereditary ACCP pulls back through an injective ring map. -/
theorem IsHereditarilyACCP.of_injective (hA : IsHereditarilyACCP A)
    (f : R →+* A) (hf : Function.Injective f) : IsHereditarilyACCP R := by
  intro S
  exact (subring_map_wfDvdMonoid_iff S f hf).mp (hA (S.map f))

/-- A hereditarily atomic domain is atomic. -/
theorem IsHereditarilyAtomic.isAtomicDomain (hR : IsHereditarilyAtomic R) :
    IsAtomicDomain R :=
  (isAtomicDomain_ringEquiv_iff (Subring.topEquiv : (⊤ : Subring R) ≃+* R)).mpr (hR ⊤)

/-- A hereditarily BF domain is BF. -/
theorem IsHereditarilyBF.isBFDomain (hR : IsHereditarilyBF R) : IsBFDomain R :=
  (isBFDomain_ringEquiv_iff (Subring.topEquiv : (⊤ : Subring R) ≃+* R)).mpr (hR ⊤)

/-- A hereditarily ACCP domain satisfies ACCP. -/
theorem IsHereditarilyACCP.wfDvdMonoid (hR : IsHereditarilyACCP R) : WfDvdMonoid R :=
  (wfDvdMonoid_ringEquiv_iff (Subring.topEquiv : (⊤ : Subring R) ≃+* R)).mpr (hR ⊤)

/-- Every subring of a hereditarily atomic domain is itself hereditarily atomic. -/
theorem IsHereditarilyAtomic.subring (hR : IsHereditarilyAtomic R) (S : Subring R) :
    IsHereditarilyAtomic S :=
  hR.of_injective S.subtype Subtype.val_injective

/-- Every subring of a hereditarily BF domain is itself hereditarily BF. -/
theorem IsHereditarilyBF.subring (hR : IsHereditarilyBF R) (S : Subring R) :
    IsHereditarilyBF S :=
  hR.of_injective S.subtype Subtype.val_injective

/-- Every subring of a hereditarily ACCP domain is itself hereditarily ACCP. -/
theorem IsHereditarilyACCP.subring (hR : IsHereditarilyACCP R) (S : Subring R) :
    IsHereditarilyACCP S :=
  hR.of_injective S.subtype Subtype.val_injective

/-- Hereditary atomicity is independent of the representation of the ambient ring. -/
theorem isHereditarilyAtomic_ringEquiv_iff (e : R ≃+* A) :
    IsHereditarilyAtomic A ↔ IsHereditarilyAtomic R :=
  ⟨fun h => h.of_injective e.toRingHom e.injective,
    fun h => h.of_injective e.symm.toRingHom e.symm.injective⟩

/-- Hereditary bounded factorization is invariant under ring equivalence. -/
theorem isHereditarilyBF_ringEquiv_iff (e : R ≃+* A) :
    IsHereditarilyBF A ↔ IsHereditarilyBF R :=
  ⟨fun h => h.of_injective e.toRingHom e.injective,
    fun h => h.of_injective e.symm.toRingHom e.symm.injective⟩

/-- Hereditary ACCP is invariant under ring equivalence. -/
theorem isHereditarilyACCP_ringEquiv_iff (e : R ≃+* A) :
    IsHereditarilyACCP A ↔ IsHereditarilyACCP R :=
  ⟨fun h => h.of_injective e.toRingHom e.injective,
    fun h => h.of_injective e.symm.toRingHom e.symm.injective⟩

end Domains

end Factorization
