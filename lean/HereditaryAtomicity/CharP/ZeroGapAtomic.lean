import Factorization.Hereditary
import Mathlib.Data.Multiset.Fintype

/-!
# Exact atomic products for the zero-gap argument

The selector argument applies to an exact product, whereas atomicity is stated
up to association. We retain that unit as one additional factor, with all
multiplicities, so the target element is unchanged. A set containing no units
and no irreducibles cannot meet every such exact factorization of a nonzero
element of an atomic domain.
-/

open scoped BigOperators

namespace HereditaryAtomicity.CharP

universe u
variable {R : Type u} [CommRing R] [IsDomain R]

/-- Atomicity gives an exact finite product of units or irreducibles. An
explicit unit factor absorbs the association without changing the target. -/
theorem exists_exact_unit_or_irreducible_factorization
    (hR : Factorization.IsAtomicDomain R) {z : R} (hz : z ≠ 0) :
    ∃ (ι : Type u) (_ : Fintype ι) (s : ι → R),
      (∏ i, s i) = z ∧ ∀ i, IsUnit (s i) ∨ Irreducible (s i) := by
  classical
  obtain ⟨s, hs, u, hu⟩ := hR z hz
  let t : Multiset R := (u : R) ::ₘ s
  refine ⟨t, inferInstance, fun i => (i : R), ?_, ?_⟩
  · rw [← Multiset.prod_eq_prod_coe]
    simpa only [t, Multiset.prod_cons, mul_comm] using hu
  · intro i
    have hi : (i : R) = (u : R) ∨ (i : R) ∈ s :=
      Multiset.mem_cons.mp (Multiset.coe_mem (x := i))
    rcases hi with hi | hi
    · apply Or.inl
      change IsUnit (i : R)
      rw [hi]
      exact u.isUnit
    · exact Or.inr (hs _ hi)

/-- If every exact finite factorization of a nonzero element meets a set with
no units or irreducibles, then the domain is not atomic. -/
theorem not_isAtomicDomain_of_factorization_meets_atomless_set
    (J : Set R) (hunit : ∀ a ∈ J, ¬ IsUnit a)
    (hatom : ∀ a ∈ J, ¬ Irreducible a)
    {z : R} (hz : z ≠ 0)
    (hmeets : ∀ (ι : Type u) [Fintype ι] (s : ι → R),
      (∏ i, s i) = z → ∃ i, s i ∈ J) :
    ¬ Factorization.IsAtomicDomain R := by
  intro hR
  obtain ⟨ι, hι, s, hs, hfac⟩ := exists_exact_unit_or_irreducible_factorization hR hz
  let := hι
  obtain ⟨i, hi⟩ := hmeets ι s hs
  exact (hfac i).elim (hunit _ hi) (hatom _ hi)

/-- It is enough to obtain the selector conclusion only for products whose
factors avoid the atomless set; atomicity supplies exactly such a product. -/
theorem not_isAtomicDomain_of_no_factorization_avoiding_atomless_set
    (J : Set R) (hunit : ∀ a ∈ J, ¬ IsUnit a)
    (hatom : ∀ a ∈ J, ¬ Irreducible a)
    {z : R} (hz : z ≠ 0)
    (hno : ∀ (ι : Type u) [Fintype ι] (s : ι → R),
      (∏ i, s i) = z → (∀ i, s i ∉ J) → False) :
    ¬ Factorization.IsAtomicDomain R := by
  intro hR
  obtain ⟨ι, hι, s, hs, hfac⟩ := exists_exact_unit_or_irreducible_factorization hR hz
  let := hι
  apply hno ι s hs
  intro i hi
  exact (hfac i).elim (hunit _ hi) (hatom _ hi)

end HereditaryAtomicity.CharP
