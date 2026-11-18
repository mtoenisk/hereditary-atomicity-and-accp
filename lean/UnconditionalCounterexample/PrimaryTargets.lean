import UnconditionalCounterexample.StageExponents
import UnconditionalCounterexample.PrimaryChoices
import UnconditionalCounterexample.PaperSquareChain

/-!
# The normalized generator targets and their requested primes

The construction order is b0, b1, q0, b2, q1, ... . Its canonical inverse gives
each zero-based raw stage the exact b/q primary profile of Section 2: b_n has order 3 at 2n; q_n has orders 2, 1, 2 at
2n, 2n+1, 2n+2. Primary/guard branch order follows Batch.branch: false is
primary and true is guard with order zero.

The finite requested prime set is exactly the image of the nonzero primary
support under the fixed prime enumeration. Every unprocessed primary has
order zero once those requests have been processed. The q integer profile is
proved equal to the profile consumed by PaperSquareChain.

These are explicit target and support calculations; realization by the
selected normalized rational functions belongs to the stage construction.
-/

namespace UnconditionalCounterexample.PrimaryTargets

open NormalizedWords

def generatorAt (k : ℕ) : Generator :=
  if k = 0 then .b 0 else if k % 2 = 1 then .b (k / 2 + 1) else .q (k / 2 - 1)

@[simp] theorem stage_generatorAt (k : ℕ) : (generatorAt k).stage = k := by
  unfold generatorAt
  split_ifs with hzero hodd
  · subst k
    rfl
  · simp only [Generator.stage]
    omega
  · simp only [Generator.stage]
    omega

@[simp] theorem generatorAt_stage (g : Generator) : generatorAt g.stage = g :=
  StageExponents.stage_injective (stage_generatorAt g.stage)

@[simp] theorem generatorAt_zero : generatorAt 0 = .b 0 := rfl

@[simp] theorem generatorAt_odd (n : ℕ) : generatorAt (2 * n + 1) = .b (n + 1) := by
  apply StageExponents.stage_injective
  rw [stage_generatorAt]
  rfl

@[simp] theorem generatorAt_even_succ (n : ℕ) : generatorAt (2 * n + 2) = .q n := by
  apply StageExponents.stage_injective
  rw [stage_generatorAt]
  rfl

def generatorEquiv : ℕ ≃ Generator where
  toFun := generatorAt
  invFun := Generator.stage
  left_inv := stage_generatorAt
  right_inv := generatorAt_stage

theorem generatorAt_injective : Function.Injective generatorAt := generatorEquiv.injective

theorem generatorAt_surjective : Function.Surjective generatorAt := generatorEquiv.surjective

/-- The prescribed natural primary order of one normalized generator. -/
def generatorOrder : Generator → ℕ → ℕ
  | .b n, j => if j = 2 * n then 3 else 0
  | .q n, j => if j = 2 * n then 2 else if j = 2 * n + 1 then 1 else if j = 2 * n + 2 then 2 else 0

/-- The exact finite set of primary coordinates with positive target order. -/
def generatorSupport : Generator → Finset ℕ
  | .b n => {2 * n}
  | .q n => {2 * n, 2 * n + 1, 2 * n + 2}

theorem mem_generatorSupport_iff (g : Generator) (j : ℕ) :
    j ∈ generatorSupport g ↔ generatorOrder g j ≠ 0 := by
  cases g with
  | b n => simp [generatorSupport, generatorOrder]
  | q n =>
    simp only [generatorSupport, Finset.mem_insert, Finset.mem_singleton]
    simp only [generatorOrder]
    split_ifs <;> omega

theorem generatorOrder_le_three (g : Generator) (j : ℕ) : generatorOrder g j ≤ 3 := by
  cases g <;> simp only [generatorOrder] <;> split_ifs <;> omega

/-- The desired primary order at the zero-based raw stage. -/
def primaryOrder (stage j : ℕ) : ℕ := generatorOrder (generatorAt stage) j

/-- Both branches are explicit: primaries take the prescribed order, guards take zero. -/
def branchOrder (stage j : ℕ) (b : Bool) : ℕ := if b then 0 else primaryOrder stage j

@[simp] theorem branchOrder_false (stage j : ℕ) : branchOrder stage j false = primaryOrder stage j := rfl
@[simp] theorem branchOrder_true (stage j : ℕ) : branchOrder stage j true = 0 := rfl

@[simp] theorem primaryOrder_generator (g : Generator) (j : ℕ) :
    primaryOrder g.stage j = generatorOrder g j := by simp only [primaryOrder, generatorAt_stage]

@[simp] theorem primaryOrder_b (n j : ℕ) :
    primaryOrder (Generator.b n).stage j = if j = 2 * n then 3 else 0 := by
  rw [primaryOrder_generator]
  rfl

@[simp] theorem primaryOrder_q (n j : ℕ) :
    primaryOrder (Generator.q n).stage j =
      if j = 2 * n then 2 else if j = 2 * n + 1 then 1 else if j = 2 * n + 2 then 2 else 0 := by
  rw [primaryOrder_generator]
  rfl

/-- The q target is exactly the integer profile consumed by the checked square chain. -/
theorem primaryOrder_q_cast (n j : ℕ) :
    (primaryOrder (Generator.q n).stage j : ℤ) = PaperSquareChain.qProfile n j := by
  rw [primaryOrder_q]
  unfold PaperSquareChain.qProfile
  split_ifs <;> rfl

/-- The finite primary indices required before choosing this raw polynomial. -/
def requiredIndices (stage : ℕ) : Finset ℕ := generatorSupport (generatorAt stage)

/-- The actual rational primes whose primaries carry nonzero target orders. -/
noncomputable def requiredPrimes (stage : ℕ) : Finset GuardSupport.PrimeIndex :=
  (requiredIndices stage).image PrimaryChoices.primes

theorem mem_requiredIndices_iff (stage j : ℕ) :
    j ∈ requiredIndices stage ↔ primaryOrder stage j ≠ 0 :=
  mem_generatorSupport_iff (generatorAt stage) j

theorem mem_requiredPrimes_iff (stage j : ℕ) :
    PrimaryChoices.primes j ∈ requiredPrimes stage ↔ primaryOrder stage j ≠ 0 := by
  rw [requiredPrimes, Finset.mem_image]
  constructor
  · rintro ⟨k, hk, heq⟩
    have hkj := PrimaryChoices.primes.injective heq
    subst k
    exact (mem_requiredIndices_iff stage j).mp hk
  · intro hj
    exact ⟨j, (mem_requiredIndices_iff stage j).mpr hj, rfl⟩

@[simp] theorem requiredPrimes_b (n : ℕ) :
    requiredPrimes (Generator.b n).stage = {PrimaryChoices.primes (2 * n)} := by
  simp [requiredPrimes, requiredIndices, generatorSupport]

@[simp] theorem requiredPrimes_q (n : ℕ) :
    requiredPrimes (Generator.q n).stage =
      {PrimaryChoices.primes (2 * n), PrimaryChoices.primes (2 * n + 1),
        PrimaryChoices.primes (2 * n + 2)} := by
  simp [requiredPrimes, requiredIndices, generatorSupport]

@[simp] theorem primaryOrder_zero (j : ℕ) : primaryOrder 0 j = if j = 0 then 3 else 0 := rfl

@[simp] theorem primaryOrder_odd (n j : ℕ) :
    primaryOrder (2 * n + 1) j = if j = 2 * n + 2 then 3 else 0 := by
  simp only [primaryOrder, generatorAt_odd, generatorOrder, Nat.mul_add, Nat.mul_one]

@[simp] theorem primaryOrder_even_succ (n j : ℕ) :
    primaryOrder (2 * n + 2) j =
      if j = 2 * n then 2 else if j = 2 * n + 1 then 1 else if j = 2 * n + 2 then 2 else 0 := by
  simp only [primaryOrder, generatorAt_even_succ, generatorOrder]

@[simp] theorem requiredPrimes_zero : requiredPrimes 0 = {PrimaryChoices.primes 0} := by
  simpa only [Generator.stage, Nat.mul_zero] using requiredPrimes_b 0

@[simp] theorem requiredPrimes_odd (n : ℕ) :
    requiredPrimes (2 * n + 1) = {PrimaryChoices.primes (2 * n + 2)} := by
  simpa only [Generator.stage, Nat.mul_add, Nat.mul_one] using requiredPrimes_b (n + 1)

@[simp] theorem requiredPrimes_even_succ (n : ℕ) :
    requiredPrimes (2 * n + 2) =
      {PrimaryChoices.primes (2 * n), PrimaryChoices.primes (2 * n + 1),
        PrimaryChoices.primes (2 * n + 2)} := requiredPrimes_q n

/-- Covering the finite requested primes covers every nonzero primary target. -/
theorem required_mem_of_order_ne_zero (stage : ℕ) (S : Finset GuardSupport.PrimeIndex)
    (hS : requiredPrimes stage ⊆ S) (j : ℕ) (hj : primaryOrder stage j ≠ 0) :
    PrimaryChoices.primes j ∈ S := hS ((mem_requiredPrimes_iff stage j).mpr hj)

/-- Every primary outside a processing set covering the requests has target order zero. -/
theorem primaryOrder_eq_zero_of_unprocessed (stage : ℕ) (S : Finset GuardSupport.PrimeIndex)
    (hS : requiredPrimes stage ⊆ S) (j : ℕ) (hj : PrimaryChoices.primes j ∉ S) :
    primaryOrder stage j = 0 := by
  by_contra h
  exact hj (required_mem_of_order_ne_zero stage S hS j h)

end UnconditionalCounterexample.PrimaryTargets
