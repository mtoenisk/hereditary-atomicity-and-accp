import UnconditionalCounterexample.MixedProfileData
import UnconditionalCounterexample.SparsePicard

/-! The Picard calculation for the literal constructed domain attached to
any infinite selected set of rational primes. All elementary construction
data and all ideal-profile realization inputs have already been proved. -/

noncomputable section
namespace UnconditionalCounterexample.MixedConstruction
open GuardSupport

variable (S : Set PrimeIndex) (hS : S.Infinite)

/-- The actual ideal class group, for every infinite selected prime set. -/
def classGroupEquiv : Additive (ClassGroup (domain S hS)) ≃+ (ℕ →₀ ZMod 3) :=
  SparsePicard.classGroupEquiv (profileData S hS)

/-- The actual Picard group, for the same literal mixed-construction domain. -/
def picardEquiv : Additive (CommRing.Pic (domain S hS)) ≃+ (ℕ →₀ ZMod 3) :=
  SparsePicard.picardEquiv (profileData S hS)

theorem classGroupConclusion : PaperTargets.ClassGroupConclusion (domain S hS) := ⟨classGroupEquiv S hS⟩

theorem picardGroupConclusion : PaperTargets.PicardGroupConclusion (domain S hS) := ⟨picardEquiv S hS⟩

end UnconditionalCounterexample.MixedConstruction
