import UnconditionalCounterexample.PaperValuations
import UnconditionalCounterexample.PaperSquareChain
import UnconditionalCounterexample.PaperInclusion

/-!
# The actual manuscript square chain and failure of ACCP

The canonical normalized q_n of PaperConstruction are units of its pole algebra,
with their actual primary and guard profiles. The existing literal square-chain
construction therefore gives endpoints t² / product(j<n, q_(2j)) in the same
domain, independent nonunit ratios q_(2j), and failure of ACCP. No selector,
profile, or chain-existence assumptions remain in these final theorems.
-/

noncomputable section
namespace UnconditionalCounterexample.PaperConstruction

open Polynomial NormalizedWords RawEvaluationPromises
local instance : Algebra ℚ (RatFunc ℚ) := RatFunc.instAlgebraOfPolynomial ℚ ℚ

/-- The literal common denominator is generated multiplicatively by earlier raws. -/
theorem rawDenominator_mem_closure (n : ℕ) :
    rawDenominator raw exponent n ∈ Submonoid.closure poles := by
  unfold rawDenominator
  apply pow_mem
  apply Submonoid.prod_mem
  intro j _
  exact Submonoid.subset_closure ⟨j.val, rfl⟩

/-- Each actual normalized generator belongs to the same pole algebra. -/
theorem generator_mem_pole (n : ℕ) : construction.chain.generators n ∈ PoleAlgebra.generated poles := by
  rw [show construction.chain.generators n =
    algebraMap ℚ[X] (RatFunc ℚ) (raw n) /
      algebraMap ℚ[X] (RatFunc ℚ) (rawDenominator raw exponent n) from
    SequenceValuations.generators_eq_quotient construction n, div_eq_mul_inv]
  exact (PoleAlgebra.generated poles).mul_mem (PoleAlgebra.polynomial_mem poles (raw n))
    (PoleAlgebra.inverse_mem_of_closure (rawDenominator_mem_closure n))

theorem generator_inv_mem_pole (n : ℕ) :
    (construction.chain.generators n)⁻¹ ∈ PoleAlgebra.generated poles := by
  rw [show construction.chain.generators n =
    algebraMap ℚ[X] (RatFunc ℚ) (raw n) /
      algebraMap ℚ[X] (RatFunc ℚ) (rawDenominator raw exponent n) from
    SequenceValuations.generators_eq_quotient construction n, inv_div, div_eq_mul_inv]
  exact (PoleAlgebra.generated poles).mul_mem
    (PoleAlgebra.polynomial_mem poles (rawDenominator raw exponent n))
    (PoleAlgebra.inverse_mem ⟨n, rfl⟩)

/-- The canonical normalized generator, viewed as an element of the pole algebra. -/
def generatorPole (n : ℕ) : PoleAlgebra.generated poles :=
  ⟨construction.chain.generators n, generator_mem_pole n⟩

theorem generatorPole_isUnit (n : ℕ) : IsUnit (generatorPole n) := by
  apply isUnit_iff_exists_inv.mpr
  refine ⟨⟨(construction.chain.generators n)⁻¹, generator_inv_mem_pole n⟩, ?_⟩
  apply Subtype.ext
  exact mul_inv_cancel₀ (construction.chain.generators_ne_zero n)

/-- These are precisely the q_n of the same selected raw family. -/
def qPole (n : ℕ) : PoleAlgebra.generated poles := generatorPole (Generator.q n).stage

@[simp] theorem qPole_coe (n : ℕ) : (qPole n : RatFunc ℚ) = construction.chain.q n := rfl

theorem qPole_isUnit (n : ℕ) : IsUnit (qPole n) := generatorPole_isUnit _

theorem qPole_primary (n j : ℕ) :
    PairedDomain.vertical places (.inl j) (qPole n : RatFunc ℚ) =
      WithZero.exp (-PaperSquareChain.qProfile n j) := by
  change PairedDomain.vertical places (.inl j)
    (CompleteProfiles.generators raw exponent (Generator.q n).stage) = _
  rw [generator_primary_valuation, PrimaryTargets.primaryOrder_q_cast]

theorem qPole_guard (n : ℕ) (p : GuardSupport.PrimeIndex) :
    PairedDomain.vertical places (.inr p) (qPole n : RatFunc ℚ) = 1 :=
  generator_guard_valuation (Generator.q n).stage p

/-- The distinguished parameter t belongs to the actual constructed domain. -/
abbrev parameter : domain := PaperInclusion.coordinate

@[simp] theorem parameter_eq_coordinate : parameter = PaperInclusion.coordinate := rfl

theorem first_primary_valuation : (places.primary 0).val.valuation = 2 := by
  change (PrimaryChoices.primary 0).val.valuation = 2
  rw [PrimaryChoices.primary_valuation]
  rfl

/-- The paper's literal chain from t², with independent ratios q_(2j),
exists in the one unconditionally constructed domain. -/
theorem squareChainConclusion : PaperTargets.SquareChainConclusion domain parameter :=
  PaperSquareChain.squareChainConclusion places qPole qPole_isUnit qPole_primary qPole_guard
    first_primary_valuation

/-- The same literal square chain proves that this actual domain fails ACCP. -/
theorem not_wfDvdMonoid : ¬ WfDvdMonoid domain :=
  PaperSquareChain.not_wfDvdMonoid places qPole qPole_isUnit qPole_primary qPole_guard
    first_primary_valuation

end UnconditionalCounterexample.PaperConstruction
