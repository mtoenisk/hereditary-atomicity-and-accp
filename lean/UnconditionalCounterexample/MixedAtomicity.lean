import UnconditionalCounterexample.MixedIntegerConductor
import UnconditionalCounterexample.MixedConstructionReturns
import UnconditionalCounterexample.ConductorFactorCounts
import UnconditionalCounterexample.FiniteDivisorBounds

/-!
# Hereditary atomicity for each actual selected-prime domain

The original unital subring remains arbitrary. Low-order bounded
factorizations and the same returned order-one divisors give strong induction
once the actual uniform integer conductor is available.
-/

namespace UnconditionalCounterexample.MixedConstruction
open GuardSupport
variable (S : Set PrimeIndex) (hS : S.Infinite)

theorem late_return (m : ℕ) (hm : 0 < m) (N : ℕ) :
    ∃ n ≥ N, (m : domain S hS) ∣ atom S hS n - 1 := by
  obtain ⟨k, hk⟩ := Filter.eventually_atTop.mp
    (MixedConstructionReturns.eventually_integer_dvd_atom_sub_one S hS m hm)
  exact ⟨max N k, le_max_left _ _, hk _ (le_max_right _ _)⟩

/-- Every unital subring of the actual sparse domain is atomic. -/
theorem hereditarilyAtomic : Factorization.IsHereditarilyAtomic (domain S hS) :=
  hereditarilyAtomic_of_integerConductors (fun z hz => (isUnit_iff_sign S hS z).mp hz)
    ((valuationProfiles S hS).value .limit) ((valuationProfiles S hS).value_mul .limit)
    (fun z hz horder => FiniteDivisorBounds.hasBoundedFactorizations_of_finite_divisor_classes hz
      (finite_associates_divisors_of_order_le_one S hS z hz (by
        rw [← valuationProfiles_limit_cast S hS z hz]
        exact_mod_cast horder)))
    (atom S hS) (atom_limit S hS)
    (fun z hz hhigh => (valuationProfiles S hS).eventually_dvd_of_primaryAtomProfiles
      (coordinate_divisibility S hS) (atom S hS) (atom_ne_zero S hS) (atom_limit S hS)
      (atom_outside S hS) (atom_primary S hS) hz hhigh)
    (late_return S hS) (MixedIntegerConductor.exists_integer_conductor S hS)

/-- Exact order-one factor count in any conductor-containing original subring. -/
theorem factor_count (T : Subring (domain S hS)) (m : ℕ) (hm : 0 < m)
    (hc : ∀ z : domain S hS, (m : domain S hS) * z ∈ T) {x : T} (hx : x ≠ 0)
    (L : Multiset T) (hatoms : ∀ z ∈ L, Irreducible z) (hprod : Associated L.prod x) :
    (L.filter (fun z : T => (valuationProfiles S hS).value .limit (z : domain S hS) = 1)).card =
      (valuationProfiles S hS).value .limit (x : domain S hS) ∧
      ∀ z ∈ L, (valuationProfiles S hS).value .limit (z : domain S hS) ≠ 1 →
        (valuationProfiles S hS).value .limit (z : domain S hS) = 0 :=
  (valuationProfiles S hS).factor_count_of_integer_conductor (coordinate_divisibility S hS)
    (atom S hS) (atom_ne_zero S hS) (atom_limit S hS) (atom_outside S hS) (atom_primary S hS)
    T m hc (late_return S hS m hm) hx L hatoms hprod

end UnconditionalCounterexample.MixedConstruction
