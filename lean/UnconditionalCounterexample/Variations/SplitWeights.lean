import Mathlib.Combinatorics.Colex
import Mathlib.Tactic.NormNum
import UnconditionalCounterexample.Variations.DyadicProfiles

/-!
# Binary corrections for the dyadic splitting construction

In the splitting construction, switching to the new tails at index `N` creates a mass
discrepancy of `k / 2 ^ N`. Its binary digits select distinct entries just
before `N`, each changed by exactly one. The lower bound on the entries
keeps every frozen fibre and the reserved balanced column untouched.
-/

namespace UnconditionalCounterexample.DyadicSplit

open DyadicProfiles

/-- Indices at which a unit correction supplies the mass `k / 2 ^ N`. -/
def correctionSites (N k : ℕ) : Finset ℕ :=
  k.bitIndices.toFinset.image (fun j => N - (j + 1))

private theorem bit_lt {j k : ℕ} (hj : j ∈ k.bitIndices.toFinset) : j < k :=
  lt_of_lt_of_le j.lt_two_pow_self (Nat.two_pow_le_of_mem_bitIndices (List.mem_toFinset.mp hj))

/-- Every correction lies between the frozen prefix and the new tail. -/
theorem correctionSites_bounds {L N k i : ℕ} (hN : L + k ≤ N)
    (hi : i ∈ correctionSites N k) : L ≤ i ∧ i < N := by
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
  have := bit_lt hj
  omega

/-- The selected half-power weights give precisely the missing tail mass. -/
theorem sum_correctionSites (N k : ℕ) (hk : k ≤ N) :
    ∑ i ∈ correctionSites N k, weight i = tailWeight N * k := by
  unfold correctionSites weight tailWeight
  rw [Finset.sum_image]
  · calc
      _ = ∑ j ∈ k.bitIndices.toFinset, (1 / 2 : ℚ) ^ N * 2 ^ j := by
        apply Finset.sum_congr rfl
        intro j hj
        have hjk := bit_lt hj
        have heq : N = (N - (j + 1) + 1) + j := by omega
        conv_rhs => lhs; rw [heq, pow_add]
        rw [mul_assoc, ← mul_pow]
        norm_num
      _ = _ := by
        rw [← Finset.mul_sum]
        congr 1
        exact_mod_cast Finset.sum_toFinset_bitIndices_two_pow k
  · intro i hi j hj hij
    have := bit_lt hi
    have := bit_lt hj
    dsimp at hij
    omega

/-- One tail cut corrects both channel masses beyond any reserved index. -/
theorem exists_split_corrections (reserved r s : ℕ) :
    ∃ N : ℕ, reserved < N ∧
      (∀ i ∈ correctionSites N s ∪ correctionSites N r, reserved < i ∧ i < N) ∧
      (∑ i ∈ correctionSites N s, weight i) = tailWeight N * s ∧
      (∑ i ∈ correctionSites N r, weight i) = tailWeight N * r := by
  let N := reserved + 1 + max r s
  have hr : reserved + 1 + r ≤ N := Nat.add_le_add_left (le_max_left _ _) _
  have hs : reserved + 1 + s ≤ N := Nat.add_le_add_left (le_max_right _ _) _
  refine ⟨N, by omega, ?_, sum_correctionSites N s (by omega), sum_correctionSites N r (by omega)⟩
  intro i hi
  rcases Finset.mem_union.mp hi with h | h
  · exact correctionSites_bounds hs h
  · exact correctionSites_bounds hr h

end UnconditionalCounterexample.DyadicSplit
