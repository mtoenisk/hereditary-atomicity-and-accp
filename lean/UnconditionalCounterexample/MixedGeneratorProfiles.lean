import UnconditionalCounterexample.MixedConstruction
import UnconditionalCounterexample.MixedSequenceValuations
import UnconditionalCounterexample.SparseProfiles

/-!
# Actual normalized generator profiles for every infinite selected prime set

The concrete MixedConstruction target policy discharges the generic local
norm and finite-support inputs. Consequently its actual normalized generators
have the prescribed b/q primary columns on the selected sequence and unit
values at every permanent guard. All polynomials, exponents, primaries and
guards are projections of that same construction. No desired generator-profile
hypothesis remains in `generatorProfiles`.
-/

noncomputable section
namespace UnconditionalCounterexample.MixedGeneratorProfiles
open Polynomial GuardSupport MixedConstruction PrimaryTargets PrimaryWordProfiles NormalizedWords

variable (S : Set PrimeIndex) (hS : S.Infinite)

/-- The global mixed branch array uses exactly the points of the actual sparse Places. -/
theorem branch_eq (j : ℕ) (b : Bool) :
    MixedSequenceArguments.branch (construction S hS) j b =
      SparsePrimaryDomain.branchAt (places S hS).primes (places S hS).primary
        (PrimaryChoices.primes j) ((places S hS).guard (PrimaryChoices.primes j)) b := rfl

/-- The static target point at a selected prime is the same point in the actual Places. -/
theorem primary_value_eq (j : ℕ)
    (hp : (primaryData S hS).paired (SelectedPrimes.primes S hS j)) :
    (primaryData S hS).value (SelectedPrimes.primes S hS j) hp = (places S hS).primary j :=
  SparsePrimaryDomain.primaryAtOf_prime (primeEmbedding S hS) _ j hp

def primaryOrderAt (n : ℕ) (p : PrimeIndex) : ℕ := MixedConstruction.branchOrder S hS n p false

theorem targetNorms : MixedSequenceValuations.TargetNorms (construction S hS) (primaryOrderAt S hS) where
  norm n i b hb := by
    calc
      _ = (((construction S hS).selection n).batch.primeAt i : ℝ) ^
          (-(MixedConstruction.branchOrder S hS n (PrimaryChoices.primes i.val) b : ℤ)) :=
        target_norm S hS ((construction S hS).chain.approx n)
          ((construction S hS).selection n).batch i b hb
      _ = _ := by cases b <;> rfl
  support n p hp := by
    classical
    have hsel : p ∈ Set.range (primeEmbedding S hS) := by
      by_contra hn
      exact hp (by simp only [primaryOrderAt, MixedConstruction.branchOrder, Bool.false_eq_true, ↓reduceIte,
        hn, ↓reduceDIte])
    obtain ⟨j, rfl⟩ := hsel
    change SelectedPrimes.primes S hS j ∈ requiredPrimes S hS n
    apply (mem_requiredPrimes_iff S hS n j).mpr
    change MixedConstruction.branchOrder S hS n (SelectedPrimes.primes S hS j) false ≠ 0 at hp
    rw [MixedConstruction.branchOrder_selected] at hp
    exact hp

/-- Exact primary column of the actual mixed normalized family at its selected index. -/
theorem generator_primary_valuation (n j : ℕ) :
    SparsePrimaryDomain.vertical (places S hS) (.inl j)
      (SparseProfiles.generators (raw S hS) (exponent S hS) n) =
        WithZero.exp (-(primaryOrder n j : ℤ)) := by
  let p := SelectedPrimes.primes S hS j
  have hp : (requirements S hS).primary.paired p := ⟨j, rfl⟩
  have hv := MixedSequenceValuations.generator_primary_valuation
    (construction S hS) (targetNorms S hS) n p hp
  have heq : (requirements S hS).primary.value p hp =
      SelectedPrimes.primary (SelectedPrimes.primes S hS) j :=
    SparsePrimaryDomain.primaryAtOf_prime (primeEmbedding S hS) _ j hp
  have he := MixedSequenceValuations.evaluationValuation_congr p.val
    ((requirements S hS).primary.transcendental p hp)
    (SelectedPrimes.primary_transcendental (SelectedPrimes.primes S hS) j)
    (congrArg (fun z : ℤ_[p.val] => z.val) heq)
  rw [he] at hv
  rw [show primaryOrderAt S hS n p = primaryOrder n j from
    MixedConstruction.branchOrder_selected S hS n j] at hv
  exact hv

/-- Every actual normalized generator has unit value at every permanent guard. -/
theorem generator_guard_valuation (n : ℕ) (p : PrimeIndex) :
    SparsePrimaryDomain.vertical (places S hS) (.inr p)
      (SparseProfiles.generators (raw S hS) (exponent S hS) n) = 1 :=
  MixedSequenceValuations.generator_guard_valuation (construction S hS) (targetNorms S hS) n p

theorem generator_b_valuation (n j : ℕ) :
    SparsePrimaryDomain.vertical (places S hS) (.inl j)
      (SparseProfiles.generators (raw S hS) (exponent S hS) (Generator.b n).stage) =
        WithZero.exp (-bWeight n j) := by
  rw [generator_primary_valuation]
  congr 1
  simp only [primaryOrder_b, bWeight]
  split_ifs <;> rfl

theorem generator_q_valuation (n j : ℕ) :
    SparsePrimaryDomain.vertical (places S hS) (.inl j)
      (SparseProfiles.generators (raw S hS) (exponent S hS) (Generator.q n).stage) =
        WithZero.exp (-qWeight n j) := by
  rw [generator_primary_valuation]
  congr 1
  rw [primaryOrder_q]
  unfold qWeight
  split_ifs <;> norm_num <;> omega

/-- The actual sparse elementary profiles, with no profile hypotheses remaining. -/
theorem generatorProfiles : SparseProfiles.GeneratorProfiles (raw S hS) (exponent S hS) (places S hS) where
  guard p n := generator_guard_valuation S hS n p
  b := generator_b_valuation S hS
  q := generator_q_valuation S hS

end UnconditionalCounterexample.MixedGeneratorProfiles
