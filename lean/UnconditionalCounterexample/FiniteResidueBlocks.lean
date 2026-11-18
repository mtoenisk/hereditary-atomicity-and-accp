import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Nat.Nth
import Mathlib.Algebra.BigOperators.Intervals

/-!
# Blocks with trivial product in a finite commutative group

Infinitely many prefix products have one repeated value. Their increasing cut
indices give nonempty consecutive blocks with product one, and every union of
consecutive selected blocks also has product one. The initial prefix may be
discarded; the first cut is not asserted to be zero.
-/

noncomputable section
namespace UnconditionalCounterexample.FiniteResidueBlocks
open scoped BigOperators

/-- Repeated prefix values yield increasing cuts at which every intervening
block has product one. -/
theorem exists_cuts {G : Type*} [CommGroup G] [Finite G] (g : ℕ → G) :
    ∃ c : ℕ → ℕ, StrictMono c ∧
      ∀ i j, i ≤ j → (∏ k ∈ Finset.Ico (c i) (c j), g k) = 1 := by
  classical
  let partialProduct (n : ℕ) : G := ∏ k ∈ Finset.range n, g k
  obtain ⟨a, ha⟩ := Finite.exists_infinite_fiber partialProduct
  have hinf : Set.Infinite {n | partialProduct n = a} := Set.infinite_coe_iff.mp ha
  let c : ℕ → ℕ := Nat.nth (fun n => partialProduct n = a)
  have hc : StrictMono c := Nat.nth_strictMono hinf
  have hvalue (n : ℕ) : partialProduct (c n) = a := Nat.nth_mem_of_infinite hinf n
  refine ⟨c, hc, ?_⟩
  intro i j hij
  rw [Finset.prod_Ico_eq_div g (hc.monotone hij)]
  change partialProduct (c j) / partialProduct (c i) = 1
  rw [hvalue j, hvalue i]
  simp

/-- Consecutive blocks and all accumulated blocks from the first selected cut
have product one in the finite residue group. -/
theorem exists_one_blocks {G : Type*} [CommGroup G] [Finite G] (g : ℕ → G) :
    ∃ c : ℕ → ℕ, StrictMono c ∧
      (∀ i, (∏ k ∈ Finset.Ico (c i) (c (i + 1)), g k) = 1) ∧
      (∀ i, (∏ k ∈ Finset.Ico (c 0) (c i), g k) = 1) := by
  obtain ⟨c, hc, hblocks⟩ := exists_cuts g
  exact ⟨c, hc, fun i => hblocks i (i+1) (Nat.le_succ i),
    fun i => hblocks 0 i (Nat.zero_le i)⟩

end UnconditionalCounterexample.FiniteResidueBlocks
