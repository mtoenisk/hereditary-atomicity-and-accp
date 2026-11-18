import UnconditionalCounterexample.MixedStageRecursion
import UnconditionalCounterexample.SparsePrimaryArguments
import UnconditionalCounterexample.PrimaryTargets
import UnconditionalCounterexample.ReturnPrefix

/-!
# The actual construction for an infinite selected prime set

The selected increasing prime sequence supplies fixed primary arguments and
the finite support of each b/q target. Active local targets are computed from
the actual preceding raw prefix, including the refined return conditions.
The mixed recursion fixes one common sequence and hence one actual sparse
intersection domain, with its fraction field and integer localization.
The later sparse profile, conductor and atomicity applications are separate.
-/

noncomputable section
namespace UnconditionalCounterexample.MixedConstruction

open Polynomial GuardSupport RecursivePrefix PrimaryTargets CombinedGuardStep

variable (S : Set PrimeIndex) (hS : S.Infinite)

/-- The static embedding of exactly the selected primes. -/
def primeEmbedding : ℕ ↪ PrimeIndex :=
  ⟨SelectedPrimes.primes S hS, SelectedPrimes.primes_injective S hS⟩

def primaryData : MixedStageRecursion.PrimaryData where
  paired p := p ∈ Set.range (primeEmbedding S hS)
  value := SparsePrimaryDomain.primaryAtOf (primeEmbedding S hS)
    (SelectedPrimes.primary (SelectedPrimes.primes S hS))
  transcendental := SparsePrimaryDomain.primaryAtOf_transcendental (primeEmbedding S hS)
    (SelectedPrimes.primary (SelectedPrimes.primes S hS))
    (SelectedPrimes.primary_transcendental (SelectedPrimes.primes S hS))
  nonunit := SparsePrimaryDomain.primaryAtOf_not_unit (primeEmbedding S hS)
    (SelectedPrimes.primary (SelectedPrimes.primes S hS))
    (SparsePrimaryDomain.selectedPrimary_not_unit (SelectedPrimes.primes S hS))

@[simp] theorem paired_iff (p : PrimeIndex) : (primaryData S hS).paired p ↔ p ∈ S := by
  change p ∈ Set.range (SelectedPrimes.primes S hS) ↔ p ∈ S
  rw [SelectedPrimes.range_primes]

/-- Actual target order at a rational prime; no primary is requested outside S. -/
def branchOrder (n : ℕ) (p : PrimeIndex) (b : Bool) : ℕ := by
  classical
  exact if b then 0 else if hp : p ∈ Set.range (primeEmbedding S hS) then
    primaryOrder n (SparsePrimaryDomain.primaryIndexOf (primeEmbedding S hS) p hp) else 0

@[simp] theorem branchOrder_true (n : ℕ) (p : PrimeIndex) : branchOrder S hS n p true = 0 := rfl

@[simp] theorem branchOrder_selected (n j : ℕ) :
    branchOrder S hS n (SelectedPrimes.primes S hS j) false = primaryOrder n j := by
  have hp : SelectedPrimes.primes S hS j ∈ Set.range (primeEmbedding S hS) := ⟨j, rfl⟩
  simp only [branchOrder, Bool.false_eq_true, ↓reduceIte, hp, ↓reduceDIte]
  exact congrArg (primaryOrder n) (SparsePrimaryDomain.primaryIndexOf_prime (primeEmbedding S hS) j hp)

/-- Required primes are exactly the finite selected primary support of this stage. -/
def requiredPrimes (n : ℕ) : Finset PrimeIndex :=
  (requiredIndices n).image (SelectedPrimes.primes S hS)

theorem mem_requiredPrimes_iff (n j : ℕ) :
    SelectedPrimes.primes S hS j ∈ requiredPrimes S hS n ↔ primaryOrder n j ≠ 0 := by
  rw [requiredPrimes, Finset.mem_image]
  constructor
  · rintro ⟨k, hk, heq⟩
    have hkj := SelectedPrimes.primes_injective S hS heq
    subst k
    exact (mem_requiredIndices_iff n j).mp hk
  · intro hj
    exact ⟨j, (mem_requiredIndices_iff n j).mpr hj, rfl⟩

/-- Active targets use the actual prefix recurrence. Unused array entries carry
no conditions and are filled with one. -/
def targets {n : ℕ} (P : Prefix n) (B : Batch) :
    MixedStageRecursion.Targets (primaryData S hS) B := by
  classical
  let d := primaryData S hS
  exact {
    value := fun i b => if hb : MixedStageSelection.Active (d.paired (PrimaryChoices.primes i.val)) b then
      P.generatorTarget (generatorAt n) (B.primeAt i) (d.branch B i b)
        (d.branch_transcendental B i b hb) (branchOrder S hS n (PrimaryChoices.primes i.val) b)
      else 1
    precision := fun i b => if hb : MixedStageSelection.Active (d.paired (PrimaryChoices.primes i.val)) b then
      P.generatorPrecision (generatorAt n) (B.primeAt i) (d.branch B i b)
        (d.branch_transcendental B i b hb) (branchOrder S hS n (PrimaryChoices.primes i.val) b)
      else 1
    nonzero := by
      intro i b hb
      rw [dite_eq_left hb]
      exact P.generatorTarget_ne_zero _ _ _ _ _ }

theorem target_norm {n : ℕ} (P : Prefix n) (B : Batch) (i : B.indices) (b : Bool)
    (hb : MixedStageSelection.Active ((primaryData S hS).paired (PrimaryChoices.primes i.val)) b) :
    ‖(targets S hS P B).value i b‖ =
      (B.primeAt i : ℝ) ^ (-(branchOrder S hS n (PrimaryChoices.primes i.val) b : ℤ)) := by
  classical
  simp only [targets, dite_eq_left hb]
  exact P.generatorTarget_norm _ _ _ _ _

def requirements : MixedStageRecursion.Requirements where
  primary := primaryData S hS
  needed := requiredPrimes S hS
  targets := targets S hS

/-- The one actual common raw/exponent/guard sequence selected for S. -/
def construction : MixedStageRecursion.Sequence (requirements S hS) :=
  MixedStageRecursion.sequence (requirements S hS)

abbrev raw := (construction S hS).chain.raw
abbrev exponent := (construction S hS).chain.exponent

/-- Primaries lie exactly over S; guards are the actual permanent choices of
this same mixed polynomial recursion. -/
def places : SparsePrimaryDomain.Places :=
  SparsePrimaryDomain.ofSelected S hS (construction S hS).chain.guardChain.value
    (construction S hS).chain.guardChain.value_transcendental

abbrev poles : Set ℚ[X] := Set.range (raw S hS)
abbrev domain : Subring (RatFunc ℚ) := SparsePrimaryDomain.domain (poles S hS) (places S hS)

theorem selected_range : Set.range (places S hS).primes = S :=
  SparsePrimaryDomain.ofSelected_range S hS _ _

theorem raw_constant {f : ℚ[X]} (hf : f ∈ poles S hS) : constantCoeff f ≠ 0 := by
  obtain ⟨j, rfl⟩ := hf
  exact (construction S hS).chain.raw_constant_ne_zero j

theorem fractionRing : IsFractionRing (domain S hS) (RatFunc ℚ) :=
  SparsePrimaryDomain.fractionRing (poles S hS) (places S hS)

theorem rational_mem_iff_integer (q : ℚ) :
    (q : RatFunc ℚ) ∈ domain S hS ↔ ∃ z : ℤ, (z : ℚ) = q :=
  SparsePrimaryDomain.rational_mem_iff_integer (poles S hS) (places S hS) q

theorem guardSupport (f : RatFunc ℚ) (hf : f ≠ 0) :
    {p : PrimeIndex | SparsePrimaryDomain.vertical (places S hS) (.inr p) f ≠ 1}.Finite :=
  (construction S hS).chain.guardChain.ratFunc_guardSupport_finite f hf

theorem integerLocalization :
    IsLocalization (IntersectionDomain.integerDenominators (domain S hS))
      (PoleAlgebra.generated (poles S hS)) :=
  SparsePrimaryDomain.integerLocalization_of_guard_support (places S hS)
    (fun _ => raw_constant S hS) (guardSupport S hS)

end UnconditionalCounterexample.MixedConstruction
