import Factorization.LengthSets
import Factorization.WeakACCP
import Mathlib.Algebra.BigOperators.Associated

/-!
# Finite factorization, almost atomicity and quasi-atomicity

Factorizations are counted up to permutation and association of the individual
factors. Almost and quasi-atomicity use multiplication inside the domain.
-/

namespace Factorization

/-- Unordered factorizations of an element into associate classes of irreducibles. -/
def atomicFactorizationClasses {R : Type*} [CommMonoid R] (x : R) : Set (Multiset (Associates R)) :=
  {s | (∀ a ∈ s, Irreducible a) ∧ s.prod = Associates.mk x}

section Monoid

variable {R : Type*} [CommMonoidWithZero R]

/-- Passing from actual factorizations to multisets of their classes gives exactly
the factorizations in the reduced monoid. -/
theorem atomicFactorizationClasses_eq_image (x : R) :
    atomicFactorizationClasses x =
      (fun s : Multiset R => s.map Associates.mk) ''
        {s | (∀ a ∈ s, Irreducible a) ∧ Associated s.prod x} := by
  ext u
  constructor
  · rintro ⟨hirr, hprod⟩
    let s : Multiset R := u.map (fun a : Associates R => Quot.out a)
    have hmap : s.map Associates.mk = u := by
      calc
        s.map Associates.mk = u.map (Associates.mk ∘ fun a : Associates R => Quot.out a) :=
          Multiset.map_map ..
        _ = u.map id := congrArg (fun f : Associates R → Associates R => u.map f)
          (funext Associates.quot_out)
        _ = u := Multiset.map_id u
    refine ⟨s, ⟨?_, Associates.mk_eq_mk_iff_associated.mp ?_⟩, hmap⟩
    · intro a ha
      apply Associates.irreducible_mk.mp
      apply hirr
      rw [← hmap]
      exact Multiset.mem_map_of_mem _ ha
    · exact Associates.prod_mk.symm.trans ((congrArg Multiset.prod hmap).trans hprod)
  · rintro ⟨s, ⟨hirr, hprod⟩, rfl⟩
    refine ⟨?_, Associates.prod_mk.trans (Associates.mk_eq_mk_iff_associated.mpr hprod)⟩
    intro a ha
    obtain ⟨p, hp, rfl⟩ := Multiset.mem_map.mp ha
    exact Associates.irreducible_mk.mpr (hirr p hp)

/-- Taking cardinalities of the factorization classes gives the usual length set. -/
theorem factorizationLengths_eq_image_card (x : R) :
    factorizationLengths x = Multiset.card '' atomicFactorizationClasses x := by
  rw [atomicFactorizationClasses_eq_image]
  ext n
  constructor
  · rintro ⟨s, hirr, hprod, rfl⟩
    exact ⟨s.map Associates.mk, ⟨s, ⟨hirr, hprod⟩, rfl⟩, Multiset.card_map _ _⟩
  · rintro ⟨_, ⟨s, ⟨hirr, hprod⟩, rfl⟩, rfl⟩
    exact ⟨s, hirr, hprod, (Multiset.card_map _ _).symm⟩

theorem atomicFactorizationClasses_nonempty_iff (x : R) :
    (atomicFactorizationClasses x).Nonempty ↔ HasAtomicFactorization x := by
  rw [← factorizationLengths_nonempty_iff, factorizationLengths_eq_image_card,
    Set.image_nonempty]

end Monoid

/-- Every nonzero element has a nonempty finite set of factorizations up to
permutation and association. -/
def IsFFDomain (R : Type*) [CommRing R] [IsDomain R] : Prop :=
  ∀ x : R, x ≠ 0 →
    (atomicFactorizationClasses x).Nonempty ∧ (atomicFactorizationClasses x).Finite

/-- Every nonzero element becomes an atomic product after multiplication by an
atomic product. Units are included via the empty factorization. -/
def IsAlmostAtomicDomain (R : Type*) [CommRing R] [IsDomain R] : Prop :=
  ∀ x : R, x ≠ 0 → ∃ a : R, HasAtomicFactorization a ∧ HasAtomicFactorization (a * x)

/-- Every nonzero element becomes an atomic product after multiplication by a
nonzero element of the same domain. -/
def IsQuasiAtomicDomain (R : Type*) [CommRing R] [IsDomain R] : Prop :=
  ∀ x : R, x ≠ 0 → ∃ y : R, y ≠ 0 ∧ HasAtomicFactorization (x * y)

variable {R : Type*} [CommRing R] [IsDomain R]

theorem HasAtomicFactorization.ne_zero {x : R} (hx : HasAtomicFactorization x) : x ≠ 0 := by
  obtain ⟨s, hirr, hprod⟩ := hx
  exact hprod.ne_zero_iff.mp (Multiset.prod_ne_zero fun h => (hirr 0 h).ne_zero rfl)

/-- A finite factorization domain is a bounded factorization domain. -/
theorem IsFFDomain.isBFDomain (hR : IsFFDomain R) : IsBFDomain R := by
  apply isBFDomain_iff_nonempty_finite_factorizationLengths.mpr
  intro x hx
  obtain ⟨hne, hfin⟩ := hR x hx
  rw [factorizationLengths_eq_image_card]
  exact ⟨hne.image _, hfin.image _⟩

theorem IsStronglyAtomicDomain.isAtomicDomain (hR : IsStronglyAtomicDomain R) : IsAtomicDomain R :=
  hR.1

theorem IsAtomicDomain.isAlmostAtomicDomain (hR : IsAtomicDomain R) : IsAlmostAtomicDomain R := by
  intro x hx
  exact ⟨1, hasAtomicFactorization_of_isUnit isUnit_one, by simpa using hR x hx⟩

theorem IsAlmostAtomicDomain.isQuasiAtomicDomain (hR : IsAlmostAtomicDomain R) :
    IsQuasiAtomicDomain R := by
  intro x hx
  obtain ⟨a, ha, hax⟩ := hR x hx
  exact ⟨a, ha.ne_zero, mul_comm a x ▸ hax⟩

/-- Quasi-atomicity is equivalently divisibility of an atomic product. -/
theorem isQuasiAtomicDomain_iff_dvd_atomic :
    IsQuasiAtomicDomain R ↔
      ∀ x : R, x ≠ 0 → ∃ z : R, HasAtomicFactorization z ∧ x ∣ z := by
  constructor
  · intro hR x hx
    obtain ⟨y, _, hxy⟩ := hR x hx
    exact ⟨x * y, hxy, dvd_mul_right x y⟩
  · intro hR x hx
    obtain ⟨_, hatom, y, rfl⟩ := hR x hx
    exact ⟨y, right_ne_zero_of_mul hatom.ne_zero, hatom⟩

end Factorization
