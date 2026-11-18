import Factorization.Basic
import Mathlib.Algebra.BigOperators.Ring.Multiset
import Mathlib.Order.Interval.Finset.Nat

/-!
# Irreducible factorization lengths and bounded factorization

Bounded factorization controls all nonunit factorizations. Its converse from
bounded irreducible lengths requires atomicity of all relevant divisors, not
just one atomic factorization of the element. The domain corollaries make this
requirement explicit through `IsAtomicDomain` and exclude zero.
-/

namespace Factorization

universe u

section Monoid

variable {R : Type u} [CommMonoid R] {x : R}

/-- A factorization length exists exactly when an atomic factorization exists. -/
theorem factorizationLengths_nonempty_iff :
    (factorizationLengths x).Nonempty ↔ HasAtomicFactorization x := by
  constructor
  · rintro ⟨n, s, hs, hx, _⟩
    exact ⟨s, hs, hx⟩
  · rintro ⟨s, hs, hx⟩
    exact ⟨s.card, s, hs, hx, rfl⟩

/-- Length zero is the empty factorization and characterizes units. -/
@[simp] theorem zero_mem_factorizationLengths_iff :
    0 ∈ factorizationLengths x ↔ IsUnit x := by
  constructor
  · rintro ⟨s, _, hsx, hcard⟩
    have hs : s = 0 := Multiset.card_eq_zero.mp hcard
    apply hsx.isUnit
    simpa only [hs, Multiset.prod_zero] using (isUnit_one : IsUnit (1 : R))
  · intro hx
    refine ⟨0, by simp, ?_, rfl⟩
    simpa using (associated_one_iff_isUnit.mpr hx).symm

/-- A product associated to a nonunit cannot be empty. -/
theorem card_pos_of_associated_prod_of_not_isUnit (s : Multiset R)
    (hsx : Associated s.prod x) (hx : ¬ IsUnit x) : 0 < s.card := by
  apply Nat.pos_of_ne_zero
  intro hcard
  have hs : s = 0 := Multiset.card_eq_zero.mp hcard
  apply hx
  apply hsx.isUnit
  simpa only [hs, Multiset.prod_zero] using (isUnit_one : IsUnit (1 : R))

/-- The sole irreducible factorization length of a unit is zero. -/
theorem factorizationLengths_eq_singleton_zero_of_isUnit (hx : IsUnit x) :
    factorizationLengths x = {0} := by
  ext n
  constructor
  · rintro ⟨s, hs, hsx, hcard⟩
    have hs0 : s = 0 := by
      by_contra hne
      obtain ⟨p, hp⟩ := Multiset.exists_mem_of_ne_zero hne
      exact (hs p hp).not_isUnit
        (isUnit_of_dvd_unit (Multiset.dvd_prod hp) (hsx.isUnit_iff.mpr hx))
    simpa only [Set.mem_singleton_iff, hs0, Multiset.card_zero] using hcard.symm
  · intro hn
    have hn0 : n = 0 := Set.mem_singleton_iff.mp hn
    subst n
    exact zero_mem_factorizationLengths_iff.mpr hx

/-- Replacing each nonunit factor by an atomic factorization can only increase
length. The result remains a factorization up to association. -/
theorem exists_irreducible_refinement (s : Multiset R)
    (hsnu : ∀ p ∈ s, ¬ IsUnit p)
    (hsatomic : ∀ p ∈ s, HasAtomicFactorization p) :
    ∃ t : Multiset R,
      (∀ p ∈ t, Irreducible p) ∧ Associated t.prod s.prod ∧ s.card ≤ t.card := by
  induction s using Multiset.induction_on with
  | empty => exact ⟨0, by simp, Associated.rfl, le_rfl⟩
  | @cons a s ih =>
    obtain ⟨aFactors, haFactors, haProduct⟩ := hsatomic a (Multiset.mem_cons_self a s)
    have haCard : 0 < aFactors.card :=
      card_pos_of_associated_prod_of_not_isUnit aFactors haProduct
        (hsnu a (Multiset.mem_cons_self a s))
    obtain ⟨t, ht, htProduct, htCard⟩ := ih
      (fun p hp => hsnu p (Multiset.mem_cons_of_mem hp))
      (fun p hp => hsatomic p (Multiset.mem_cons_of_mem hp))
    refine ⟨aFactors + t, ?_, ?_, ?_⟩
    · intro p hp
      rcases Multiset.mem_add.mp hp with hpa | hpt
      · exact haFactors p hpa
      · exact ht p hpt
    · simpa only [Multiset.prod_add, Multiset.prod_cons] using haProduct.mul_mul htProduct
    · simp only [Multiset.card_cons, Multiset.card_add]
      omega

/-- A nonunit factorization of an element with atomic divisors refines to an
irreducible factorization of that element of at least the original length. -/
theorem exists_factorizationLength_ge_card_of_atomic_divisors
    (hatomic : ∀ p : R, p ∣ x → HasAtomicFactorization p)
    (s : Multiset R) (hsnu : ∀ p ∈ s, ¬ IsUnit p) (hsx : Associated s.prod x) :
    ∃ n ∈ factorizationLengths x, s.card ≤ n := by
  obtain ⟨t, ht, hts, hcard⟩ := exists_irreducible_refinement s hsnu
    (fun p hp => hatomic p ((Multiset.dvd_prod hp).trans hsx.dvd))
  exact ⟨t.card, ⟨t, ht, hts.trans hsx, rfl⟩, hcard⟩

/-- Bounds on all nonunit factorizations bound irreducible lengths. -/
theorem HasBoundedFactorizations.bddAbove_factorizationLengths
    (hx : HasBoundedFactorizations x) : BddAbove (factorizationLengths x) := by
  obtain ⟨N, hN⟩ := hx
  refine ⟨N, ?_⟩
  rintro n ⟨s, hs, hsx, hcard⟩
  rw [← hcard]
  exact hN s (fun p hp => (hs p hp).not_isUnit) hsx

/-- Bounded factorization makes the set of irreducible lengths finite. -/
theorem HasBoundedFactorizations.finite_factorizationLengths
    (hx : HasBoundedFactorizations x) : (factorizationLengths x).Finite :=
  Set.finite_iff_bddAbove.mpr hx.bddAbove_factorizationLengths

/-- Atomicity of the divisors allows a bound on irreducible lengths to control
all nonunit factorizations. No chain condition is assumed. -/
theorem hasBoundedFactorizations_of_bddAbove_factorizationLengths_of_atomic_divisors
    (hatomic : ∀ p : R, p ∣ x → HasAtomicFactorization p)
    (hbound : BddAbove (factorizationLengths x)) : HasBoundedFactorizations x := by
  obtain ⟨N, hN⟩ := hbound
  refine ⟨N, ?_⟩
  intro s hsnu hsx
  obtain ⟨n, hn, hcard⟩ :=
    exists_factorizationLength_ge_card_of_atomic_divisors hatomic s hsnu hsx
  exact hcard.trans (hN hn)

end Monoid

section Domain

variable {R : Type u} [CommRing R] [IsDomain R] {x : R}

/-- Zero has no irreducible factorization in a domain. -/
@[simp] theorem factorizationLengths_zero :
    factorizationLengths (0 : R) = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro n ⟨s, hs, hsx, _⟩
  have hprod : s.prod ≠ 0 := Multiset.prod_ne_zero (fun hzero => (hs 0 hzero).ne_zero rfl)
  exact hprod ((associated_zero_iff_eq_zero _).mp hsx)

/-- Zero admits arbitrarily long nonunit factorizations, unlike units. -/
theorem not_hasBoundedFactorizations_zero : ¬ HasBoundedFactorizations (0 : R) := by
  rintro ⟨N, hN⟩
  have hbound := hN (Multiset.replicate (N + 1) (0 : R)) (by
    intro p hp
    obtain ⟨_, rfl⟩ := Multiset.mem_replicate.mp hp
    exact not_isUnit_zero) (by simp)
  simp only [Multiset.card_replicate] at hbound
  omega

/-- Every nonzero element of an atomic domain has at least one factorization length. -/
theorem IsAtomicDomain.factorizationLengths_nonempty (hR : IsAtomicDomain R)
    (hx : x ≠ 0) : (factorizationLengths x).Nonempty :=
  factorizationLengths_nonempty_iff.mpr (hR x hx)

/-- In an atomic domain, bounded irreducible lengths characterize BF for a
nonzero element. Global atomicity supplies factorizations of all its divisors. -/
theorem hasBoundedFactorizations_iff_bddAbove_factorizationLengths
    (hR : IsAtomicDomain R) (hx : x ≠ 0) :
    HasBoundedFactorizations x ↔ BddAbove (factorizationLengths x) := by
  constructor
  · exact HasBoundedFactorizations.bddAbove_factorizationLengths
  · exact hasBoundedFactorizations_of_bddAbove_factorizationLengths_of_atomic_divisors
      (fun p hp => hR p (ne_zero_of_dvd_ne_zero hx hp))

/-- In an atomic domain, finite irreducible length sets characterize BF for
nonzero elements. The nonzero restriction is essential. -/
theorem hasBoundedFactorizations_iff_finite_factorizationLengths
    (hR : IsAtomicDomain R) (hx : x ≠ 0) :
    HasBoundedFactorizations x ↔ (factorizationLengths x).Finite :=
  (hasBoundedFactorizations_iff_bddAbove_factorizationLengths hR hx).trans
    Set.finite_iff_bddAbove.symm

/-- Atomicity is exactly nonemptiness of every nonzero element's length set. -/
theorem isAtomicDomain_iff_nonempty_factorizationLengths :
    IsAtomicDomain R ↔ ∀ x : R, x ≠ 0 → (factorizationLengths x).Nonempty := by
  constructor
  · intro hR x hx
    exact hR.factorizationLengths_nonempty hx
  · intro hR x hx
    exact factorizationLengths_nonempty_iff.mp (hR x hx)

/-- The conventional atomic-plus-finite-length-sets definition agrees with the
bound on all nonunit factorizations. -/
theorem isBFDomain_iff_isAtomicDomain_and_finite_factorizationLengths :
    IsBFDomain R ↔ IsAtomicDomain R ∧
      ∀ x : R, x ≠ 0 → (factorizationLengths x).Finite := by
  constructor
  · intro hR
    exact ⟨fun x hx => (hR x hx).hasAtomicFactorization,
      fun x hx => (hR x hx).finite_factorizationLengths⟩
  · rintro ⟨hR, hfinite⟩ x hx
    exact (hasBoundedFactorizations_iff_finite_factorizationLengths hR hx).mpr
      (hfinite x hx)

/-- Equivalently, every nonzero element has a nonempty finite length set. -/
theorem isBFDomain_iff_nonempty_finite_factorizationLengths :
    IsBFDomain R ↔ ∀ x : R, x ≠ 0 →
      (factorizationLengths x).Nonempty ∧ (factorizationLengths x).Finite := by
  rw [isBFDomain_iff_isAtomicDomain_and_finite_factorizationLengths,
    isAtomicDomain_iff_nonempty_factorizationLengths]
  constructor
  · rintro ⟨hnonempty, hfinite⟩ x hx
    exact ⟨hnonempty x hx, hfinite x hx⟩
  · intro hR
    exact ⟨fun x hx => (hR x hx).1, fun x hx => (hR x hx).2⟩

end Domain

end Factorization
