import UnconditionalCounterexample.EvaluationChoices
import UnconditionalCounterexample.GuardSupport
import Mathlib.Order.OrderIsoNat
import Mathlib.Data.Nat.PrimeFin

/-!
# Increasing enumeration and the exceptional primary argument

The guard choices depend on earlier raw polynomials. The primary arguments
only depend on the prime index, so their family can be fixed at the start
and used as each prime is assigned in Section 3 of the manuscript.
-/
noncomputable section
namespace UnconditionalCounterexample.PrimaryChoices
open GuardSupport

/-- The increasing enumeration from §2. -/
def primes : ℕ ≃o PrimeIndex :=
  @Nat.Subtype.orderIsoOfNat (Set.ofPred Nat.Prime) Nat.infinite_setOfPred_prime.to_subtype

def order (j : ℕ) : ℤ := if j = 0 then 2 else 1

theorem exists_primary (j : ℕ) : ∃ z : ℤ_[(primes j).val],
    Transcendental ℚ z.val ∧ z.val.valuation = order j := by
  obtain ⟨x, ht, _, hv⟩ := EvaluationChoices.exists_transcendental_valuation (primes j).val (order j)
  have h : 0 ≤ order j := by unfold order; split <;> decide
  exact ⟨⟨x, (Padic.norm_le_one_iff_val_nonneg x).mpr (hv ▸ h)⟩, ht, hv⟩

def primary (j : ℕ) : ℤ_[(primes j).val] := (exists_primary j).choose

theorem primary_transcendental (j : ℕ) : Transcendental ℚ (primary j).val :=
  (exists_primary j).choose_spec.1

theorem primary_valuation (j : ℕ) : (primary j).val.valuation = order j :=
  (exists_primary j).choose_spec.2

@[simp] theorem primary_zero : (primary 0).val.valuation = 2 := by
  exact primary_valuation 0

theorem primary_late (j : ℕ) (hj : 0 < j) : (primary j).val.valuation = 1 := by
  rw [primary_valuation]; simp [order, Nat.ne_of_gt hj]

end UnconditionalCounterexample.PrimaryChoices
