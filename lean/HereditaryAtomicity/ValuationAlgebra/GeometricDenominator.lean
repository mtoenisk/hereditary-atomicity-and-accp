import Mathlib.Algebra.Ring.GeomSum
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Algebra.CharP.Basic
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Data.Set.Finite.Lattice

/-!
# Geometric denominators avoiding finitely many residues

For a fixed element of a nontrivial ring, a geometric sum of prime length can
vanish for at most one prime length. This permits the same denominator to be a
unit in a finite family of valuation rings when its argument is integral there.
-/

namespace HereditaryAtomicity.ValuationAlgebra

open Finset

/-- Two vanishing geometric sums of prime length have the same length. -/
theorem prime_eq_of_geomSum_eq_zero {R : Type*} [Ring R] [Nontrivial R]
    (x : R) {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hxp : ∑ j ∈ range p, x ^ j = 0) (hxq : ∑ j ∈ range q, x ^ j = 0) : p = q := by
  by_contra hpq
  have hpowp : x ^ p = 1 := by
    have h := geom_sum_mul x p
    rw [hxp, zero_mul] at h
    exact sub_eq_zero.mp h.symm
  have hpowq : x ^ q = 1 := by
    have h := geom_sum_mul x q
    rw [hxq, zero_mul] at h
    exact sub_eq_zero.mp h.symm
  have hx : x = 1 := by
    apply orderOf_eq_one_iff.mp
    apply Nat.dvd_one.mp
    have hdiv := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hpowp)
      (orderOf_dvd_of_pow_eq_one hpowq)
    rwa [((Nat.coprime_primes hp hq).mpr hpq).gcd_eq_one] at hdiv
  have hpc : (p : R) = 0 := by simpa only [hx, one_pow, sum_const, card_range,
    nsmul_eq_mul, mul_one] using hxp
  have hqc : (q : R) = 0 := by simpa only [hx, one_pow, sum_const, card_range,
    nsmul_eq_mul, mul_one] using hxq
  exact hpq ((CharP.ringChar_of_prime_eq_zero hp hpc).symm.trans
    (CharP.ringChar_of_prime_eq_zero hq hqc))

/-- The set of prime lengths at which one geometric sum vanishes is subsingleton. -/
theorem bad_geomSum_primes_subsingleton {R : Type*} [Ring R] [Nontrivial R] (x : R) :
    {p : ℕ | p.Prime ∧ ∑ j ∈ range p, x ^ j = 0}.Subsingleton := by
  intro p hp q hq
  exact prime_eq_of_geomSum_eq_zero x hp.1 hq.1 hp.2 hq.2

/-- A finite family of elements, even in different rings, admits a common
prime length at which every geometric sum is nonzero. -/
theorem exists_prime_geomSum_ne_zero {ι : Type*} [Finite ι]
    (R : ι → Type*) [∀ i, Ring (R i)] [∀ i, Nontrivial (R i)] (x : ∀ i, R i) :
    ∃ p : ℕ, p.Prime ∧ ∀ i, ∑ j ∈ range p, (x i) ^ j ≠ 0 := by
  let bad : ι → Set ℕ := fun i => {p | p.Prime ∧ ∑ j ∈ range p, (x i) ^ j = 0}
  have hfinite : (⋃ i, bad i).Finite :=
    Set.finite_iUnion fun i => (bad_geomSum_primes_subsingleton (x i)).finite
  obtain ⟨p, hp, hgood⟩ := Nat.infinite_setOfPred_prime.exists_notMem_finite hfinite
  refine ⟨p, hp, ?_⟩
  intro i hzero
  exact hgood (Set.mem_iUnion.mpr ⟨i, hp, hzero⟩)

end HereditaryAtomicity.ValuationAlgebra
