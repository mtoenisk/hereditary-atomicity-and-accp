import UnconditionalCounterexample.PaperConstruction
import UnconditionalCounterexample.SequenceValuations
import UnconditionalCounterexample.CompleteProfiles

/-!
# Actual primary and guard columns for the manuscript construction

The concrete ordinary/refined b/q target policy satisfies the finite norm and
support specification. The one recursively selected family therefore realizes
all primary and guard columns on the same PaperConstruction.domain. These are
unconditional column theorems, with no remaining profile or selector premises.
-/

namespace UnconditionalCounterexample.PaperConstruction

open Polynomial StageRecursion PrimaryTargets SequenceValuations PrimaryWordProfiles NormalizedWords

/-- The concrete b/q policy has the required primary targets, guard target zero,
and includes every prime supporting a nonzero primary target. -/
theorem targetNorms : TargetNorms construction primaryOrder where
  norm n i b := by
    have h := target_norm (construction.chain.approx n) (construction.selection n).batch i b
    cases b <;> exact h
  support n j hj := (mem_requiredPrimes_iff n j).mpr hj

/-- The actual primary column of every globally selected normalized generator. -/
theorem generator_primary_valuation (n j : ℕ) :
    PairedDomain.vertical places (.inl j)
      (CompleteProfiles.generators raw exponent n) = WithZero.exp (-(primaryOrder n j : ℤ)) :=
  SequenceValuations.generator_primary_valuation construction targetNorms n j

/-- Every guard evaluates every actual normalized generator to a unit. -/
theorem generator_guard_valuation (n : ℕ) (p : GuardSupport.PrimeIndex) :
    PairedDomain.vertical places (.inr p) (CompleteProfiles.generators raw exponent n) = 1 :=
  SequenceValuations.generator_guard_valuation construction targetNorms n p

/-- The exact b column, including the exceptional first primary. -/
theorem generator_b_valuation (n j : ℕ) :
    PairedDomain.vertical places (.inl j)
      (CompleteProfiles.generators raw exponent (Generator.b n).stage) = WithZero.exp (-(bWeight n j)) := by
  rw [generator_primary_valuation]
  congr 1
  simp only [primaryOrder_b, bWeight]
  split_ifs <;> rfl

/-- The exact q column at its three prescribed primaries. -/
theorem generator_q_valuation (n j : ℕ) :
    PairedDomain.vertical places (.inl j)
      (CompleteProfiles.generators raw exponent (Generator.q n).stage) = WithZero.exp (-(qWeight n j)) := by
  rw [generator_primary_valuation]
  congr 1
  rw [primaryOrder_q]
  unfold qWeight
  split_ifs <;> norm_num <;> omega

/-- All elementary valuation columns now belong to the same actual construction. -/
theorem generatorProfiles : CompleteProfiles.GeneratorProfiles raw exponent places where
  guard p n := generator_guard_valuation n p
  b := generator_b_valuation
  q := generator_q_valuation

end UnconditionalCounterexample.PaperConstruction
