import UnconditionalCounterexample.SparseSquareChain
import UnconditionalCounterexample.SparseProfileData
import UnconditionalCounterexample.SparseDomainValues

noncomputable section
namespace UnconditionalCounterexample.SparseSquareWitness
open Polynomial NormalizedWords WithZero SparseProfileData
local instance : Algebra ℚ (RatFunc ℚ) := RatFunc.instAlgebraOfPolynomial ℚ ℚ
variable (A : Data)

/-- The literal normalized raw generator in its pole algebra. -/
def generatorPole (n : ℕ) : PoleAlgebra.generated A.poles :=
  ⟨A.generators n, (AtomProfiles.generators_pole_unit A.raw A.exponent n).1⟩

theorem generatorPole_isUnit (n : ℕ) : IsUnit (generatorPole A n) := by
  apply isUnit_iff_exists_inv.mpr
  refine ⟨⟨(A.generators n)⁻¹, (AtomProfiles.generators_pole_unit A.raw A.exponent n).2⟩, ?_⟩
  apply Subtype.ext
  exact mul_inv_cancel₀ (A.generators_ne_zero n)

/-- The q_n from the same actual raw sequence. -/
def qPole (n : ℕ) : PoleAlgebra.generated A.poles := generatorPole A (Generator.q n).stage

@[simp] theorem qPole_coe (n : ℕ) : (qPole A n : RatFunc ℚ) =
    ReturnPrefix.q A.generators n := rfl

theorem qPole_isUnit (n : ℕ) : IsUnit (qPole A n) := generatorPole_isUnit A _

theorem qPole_primary (n j : ℕ) :
    SparsePrimaryDomain.vertical A.places (.inl j) (qPole A n : RatFunc ℚ) =
      exp (-PaperSquareChain.qProfile n j) := by
  change SparsePrimaryDomain.vertical A.places (.inl j)
    (SparseProfiles.generators A.raw A.exponent (Generator.q n).stage) = _
  rw [A.columns.q]
  congr 2
  unfold PrimaryWordProfiles.qWeight PaperSquareChain.qProfile
  split_ifs <;> omega

theorem qPole_guard (n : ℕ) (p : GuardSupport.PrimeIndex) :
    SparsePrimaryDomain.vertical A.places (.inr p) (qPole A n : RatFunc ℚ) = 1 :=
  A.columns.guard p (Generator.q n).stage

abbrev parameter : A.domain := SparseDomainValues.coordinate A.poles A.places

theorem squareChainConclusion : PaperTargets.SquareChainConclusion A.domain (parameter A) :=
  SparseSquareChain.squareChainConclusion A.places (qPole A) (qPole_isUnit A)
    (qPole_primary A) (qPole_guard A) A.first

theorem not_wfDvdMonoid : ¬ WfDvdMonoid A.domain :=
  SparseSquareChain.not_wfDvdMonoid A.places (qPole A) (qPole_isUnit A)
    (qPole_primary A) (qPole_guard A) A.first

end UnconditionalCounterexample.SparseSquareWitness
