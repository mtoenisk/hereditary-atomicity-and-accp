import UnconditionalCounterexample.TripleCongruence
import Factorization.Bounds

/-!
# Valuation profile interface for the guarded construction

The data are natural orders on nonzero elements of the actual domain. Zero
values are deliberately unconstrained. This interface asserts neither the
existence of the domain nor atomicity; the construction must supply its laws.
-/

namespace UnconditionalCounterexample

universe u v

/-- The horizontal limit, primary sequence, and other defining valuations. -/
inductive ProfilePlace (ι : Type v)
  | limit
  | primary (n : ℕ)
  | outside (i : ι)
  deriving DecidableEq

/-- The precise profile facts needed for low-order bounded factorization. -/
structure ValuationProfiles (R : Type u) (ι : Type v)
    [CommRing R] [IsDomain R] where
  value : ProfilePlace ι → R → ℕ
  value_unit : ∀ p x, IsUnit x → value p x = 0
  value_mul : ∀ p x y, x ≠ 0 → y ≠ 0 → value p (x * y) = value p x + value p y
  unit_of_zero : ∀ x, x ≠ 0 → (∀ p, value p x = 0) → IsUnit x
  eventually_primary : ∀ x, x ≠ 0 → ∃ N : ℕ, ∀ n, N ≤ n →
    value (.primary n) x = value .limit x
  finite_outside : ∀ x, x ≠ 0 → {i | value (.outside i) x ≠ 0}.Finite
  pure_triple : ∀ x, x ≠ 0 → value .limit x = 0 →
    (∀ i, value (.outside i) x = 0) →
    TripleCongruent (fun n => (value (.primary n) x : ℤ))

namespace ValuationProfiles

variable {R : Type u} {ι : Type v} [CommRing R] [IsDomain R]

/-- Divisibility of nonzero elements is monotone at every profile coordinate. -/
theorem value_le_of_dvd (v : ValuationProfiles R ι) (p : ProfilePlace ι)
    {x y : R} (hy : y ≠ 0) (hxy : x ∣ y) : v.value p x ≤ v.value p y := by
  obtain ⟨z, rfl⟩ := hxy
  rw [v.value_mul p x z (left_ne_zero_of_mul hy) (right_ne_zero_of_mul hy)]
  exact Nat.le_add_right _ _

end ValuationProfiles
end UnconditionalCounterexample
