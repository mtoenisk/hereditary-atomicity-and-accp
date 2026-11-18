import UnconditionalCounterexample.MixedProfileData
import UnconditionalCounterexample.SparseSquareWitness

/-!
# The actual square chain for every infinite selected prime set

The ratios and endpoints are those of the single mixed raw sequence for S.
No profile, chain-existence or other construction hypotheses remain.
-/

noncomputable section
namespace UnconditionalCounterexample.MixedConstruction
open GuardSupport
variable (S : Set PrimeIndex) (hS : S.Infinite)

/-- The original rational coordinate in the actual sparse intersection. -/
abbrev parameter : domain S hS := SparseDomainValues.coordinate (poles S hS) (places S hS)

@[simp] theorem coe_parameter : (parameter S hS : RatFunc ℚ) = RatFunc.X := rfl

/-- The same canonical q_n from the mixed normalized-generator sequence. -/
abbrev qPole (n : ℕ) : PoleAlgebra.generated (poles S hS) :=
  SparseSquareWitness.qPole (profileData S hS) n

@[simp] theorem qPole_coe (n : ℕ) : (qPole S hS n : RatFunc ℚ) =
    (construction S hS).chain.q n := rfl

/-- The literal chain starting at t², with its own independent even ratios. -/
theorem squareChainConclusion : PaperTargets.SquareChainConclusion (domain S hS) (parameter S hS) :=
  SparseSquareWitness.squareChainConclusion (profileData S hS)

/-- The actual sparse example fails ACCP. -/
theorem not_wfDvdMonoid : ¬ WfDvdMonoid (domain S hS) :=
  SparseSquareWitness.not_wfDvdMonoid (profileData S hS)

end UnconditionalCounterexample.MixedConstruction
