import Factorization.Definitions
import Mathlib.Data.Finset.Image

/-!
# Common divisors leaving a cofactor of low order

For a nonempty finite family of nonzero elements, divide the whole family
by an element of order one whenever every member has order at least two.
An additive natural order bounds the number of steps.
-/

namespace Factorization

variable {R : Type*} [CommMonoidWithZero R]

/-- If every finite family of high-order elements has a common divisor of
order one, arbitrary finite families admit a common divisor leaving at
least one of their original members with a cofactor of order at most one. -/
theorem exists_common_dvd_lowOrder
    (ord : R → ℕ)
    (hmul : ∀ a b : R, a ≠ 0 → b ≠ 0 → ord (a * b) = ord a + ord b)
    (hcommon : ∀ s : Finset R, s.Nonempty → (∀ x ∈ s, x ≠ 0) →
      (∀ x ∈ s, 2 ≤ ord x) → ∃ d : R, ord d = 1 ∧ ∀ x ∈ s, d ∣ x)
    (s : Finset R) (hs : s.Nonempty) (hzero : ∀ x ∈ s, x ≠ 0) :
    ∃ d : R, (∀ x ∈ s, d ∣ x) ∧ ∃ x ∈ s, ∃ q : R, x = d * q ∧ ord q ≤ 1 := by
  classical
  obtain ⟨base, hbase⟩ := hs
  generalize hn : ord base = n
  induction n using Nat.strong_induction_on generalizing s base with
  | h n ih =>
    by_cases hlow : ∃ x ∈ s, ord x ≤ 1
    · obtain ⟨x, hx, hxlow⟩ := hlow
      exact ⟨1, fun y _ => one_dvd y, x, hx, x, (one_mul x).symm, hxlow⟩
    have hhigh (x : R) (hx : x ∈ s) : 2 ≤ ord x := by
      have hxhigh : ¬ ord x ≤ 1 := fun h => hlow ⟨x, hx, h⟩
      omega
    obtain ⟨c, hc, hdiv⟩ := hcommon s ⟨base, hbase⟩ hzero hhigh
    let q (x : R) : R := if hx : x ∈ s then (hdiv x hx).choose else 0
    have hq (x : R) (hx : x ∈ s) : x = c * q x := by
      simpa only [q, dite_eq_left hx] using (hdiv x hx).choose_spec
    have hprod (x : R) (hx : x ∈ s) : c * q x ≠ 0 := by
      rw [← hq x hx]
      exact hzero x hx
    have hqzero (y : R) (hy : y ∈ s.image q) : y ≠ 0 := by
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
      exact right_ne_zero_of_mul (hprod x hx)
    have hlt : ord (q base) < n := by
      have hsum := hmul c (q base) (left_ne_zero_of_mul (hprod base hbase))
        (right_ne_zero_of_mul (hprod base hbase))
      rw [← hq base hbase, hn, hc] at hsum
      omega
    obtain ⟨d, hd, y, hy, z, hyz, hz⟩ :=
      ih (ord (q base)) hlt (s.image q) hqzero (q base) (Finset.mem_image_of_mem q hbase) rfl
    refine ⟨c * d, ?_, ?_⟩
    · intro x hx
      obtain ⟨u, hu⟩ := hd (q x) (Finset.mem_image_of_mem q hx)
      exact ⟨u, (hq x hx).trans (by rw [hu, mul_assoc])⟩
    · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
      exact ⟨x, hx, z, (hq x hx).trans (by rw [hyz, mul_assoc]), hz⟩

end Factorization
