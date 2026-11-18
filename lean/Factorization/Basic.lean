import Factorization.Definitions
import Mathlib.Data.Nat.Find

/-!
# Bounded factorization gives atomic factorization

General commutative-monoid factorization foundations. The maximum-length
argument does not use a well-founded divisibility relation.
-/

namespace Factorization

variable {R : Type*} [CommMonoid R] {x y : R}

/-- Associated elements have the same existence of atomic factorizations. -/
theorem HasAtomicFactorization.associated (hx : HasAtomicFactorization x)
    (hxy : Associated x y) : HasAtomicFactorization y := by
  obtain ⟨s, hs, hsx⟩ := hx
  exact ⟨s, hs, hsx.trans hxy⟩

/-- Associated elements have the same nonunit factorization bounds. -/
theorem HasBoundedFactorizations.associated (hx : HasBoundedFactorizations x)
    (hxy : Associated x y) : HasBoundedFactorizations y := by
  obtain ⟨N, hN⟩ := hx
  exact ⟨N, fun s hs hsy => hN s hs (hsy.trans hxy.symm)⟩

/-- Irreducible factorization lengths depend only on the associate class. -/
theorem factorizationLengths_eq_of_associated (hxy : Associated x y) :
    factorizationLengths x = factorizationLengths y := by
  ext n
  constructor
  · rintro ⟨s, hs, hsx, hcard⟩
    exact ⟨s, hs, hsx.trans hxy, hcard⟩
  · rintro ⟨s, hs, hsy, hcard⟩
    exact ⟨s, hs, hsy.trans hxy.symm, hcard⟩

/-- A unit is represented by the empty irreducible factorization. -/
theorem hasAtomicFactorization_of_isUnit (hx : IsUnit x) : HasAtomicFactorization x := by
  refine ⟨0, by simp, ?_⟩
  simpa using (associated_one_iff_isUnit.mpr hx).symm

/-- An irreducible element has its singleton factorization. -/
theorem hasAtomicFactorization_of_irreducible (hx : Irreducible x) :
    HasAtomicFactorization x := by
  refine ⟨{x}, ?_, ?_⟩
  · simpa using hx
  · simp

/-- Atomic factorizations concatenate under multiplication. -/
theorem HasAtomicFactorization.mul (hx : HasAtomicFactorization x)
    (hy : HasAtomicFactorization y) : HasAtomicFactorization (x * y) := by
  obtain ⟨s, hs, hsx⟩ := hx
  obtain ⟨t, ht, hty⟩ := hy
  refine ⟨s + t, ?_, ?_⟩
  · intro p hp
    rcases Multiset.mem_add.mp hp with hp | hp
    · exact hs p hp
    · exact ht p hp
  · simpa using hsx.mul_mul hty

/-- Powers preserve existence of an atomic factorization, including the zero power. -/
theorem HasAtomicFactorization.pow (hx : HasAtomicFactorization x) (n : ℕ) :
    HasAtomicFactorization (x ^ n) := by
  induction n with
  | zero => simpa using hasAtomicFactorization_of_isUnit (isUnit_one : IsUnit (1 : R))
  | succ n ih => simpa [pow_succ] using ih.mul hx

/-- Bounded lengths of all nonunit factorizations give a factorization of maximum
length; every factor in it must be irreducible. No divisibility chain condition or
cancellation assumption is needed. -/
theorem HasBoundedFactorizations.hasAtomicFactorization (hx : HasBoundedFactorizations x) :
    HasAtomicFactorization x := by
  classical
  by_cases hxu : IsUnit x
  · exact hasAtomicFactorization_of_isUnit hxu
  obtain ⟨N, hN⟩ := hx
  let P : ℕ → Prop := fun n => ∃ s : Multiset R,
    (∀ p ∈ s, ¬ IsUnit p) ∧ Associated s.prod x ∧ s.card = n
  have hPone : P 1 := by
    refine ⟨{x}, ?_, ?_, by simp⟩
    · simpa using hxu
    · simp
  have honeN : 1 ≤ N := by
    obtain ⟨s, hs, hsx, hscard⟩ := hPone
    simpa [hscard] using hN s hs hsx
  obtain ⟨s, hs, hsx, hscard⟩ := Nat.findGreatest_spec honeN hPone
  refine ⟨s, ?_, hsx⟩
  intro p hp
  rcases irreducible_or_factor (hs p hp) with hirr | ⟨a, b, ha, hb, hab⟩
  · exact hirr
  exfalso
  let t := a ::ₘ b ::ₘ s.erase p
  have ht : ∀ q ∈ t, ¬ IsUnit q := by
    intro q hq
    simp only [t, Multiset.mem_cons] at hq
    rcases hq with rfl | rfl | hq
    · exact ha
    · exact hb
    · exact hs q (Multiset.mem_of_mem_erase hq)
  have htprod : t.prod = s.prod := by
    dsimp [t]
    rw [Multiset.prod_cons, Multiset.prod_cons, ← mul_assoc, ← hab,
      Multiset.prod_erase hp]
  have htx : Associated t.prod x := by simpa only [htprod] using hsx
  have htN := hN t ht htx
  have hPcard : P t.card := ⟨t, ht, htx, rfl⟩
  have hmax := Nat.le_findGreatest htN hPcard
  have hcardpos : 0 < s.card := Multiset.card_pos.mpr (by
    intro hs0
    simp [hs0] at hp)
  have hcard : t.card = s.card + 1 := by
    dsimp [t]
    rw [Multiset.card_cons, Multiset.card_cons, Multiset.card_erase_of_mem hp,
      Nat.pred_eq_sub_one]
    omega
  omega

end Factorization
