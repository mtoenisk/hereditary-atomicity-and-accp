import UnconditionalCounterexample.PaperAtomicity
import UnconditionalCounterexample.PaperSubrings
import UnconditionalCounterexample.PaperSP
import UnconditionalCounterexample.PaperPicard

/-!
# Theorems A and B of the manuscript

Both assertions concern the subring of ℚ(t) defined by the single recursive
construction. The witnesses of the square chain and its independence are the
same even-indexed ratios. The classification ranges over all unital subrings
of this very domain.
-/

namespace UnconditionalCounterexample
namespace PaperConstruction

/-- Theorem A for the explicit subring of the rational function field. -/
theorem theoremAConclusion : PaperTargets.TheoremAConclusion domain :=
  ⟨hereditarilyAtomic, fractionRing, isUnit_iff_sign,
    ⟨parameter, rfl, parameter_irreducible, squareChainConclusion⟩, not_wfDvdMonoid,
    isAlmostDedekindDomain, isSPDomain, PaperPicard.picardGroupConclusion⟩

/-- Theorems A and B for the same witness. -/
theorem paperConclusion : PaperTargets.PaperConclusion domain :=
  ⟨theoremAConclusion, theoremBConclusion⟩

end PaperConstruction

/-- Existence with the complete conclusions of the two main theorems. -/
theorem paperCounterexampleExists : PaperTargets.PaperCounterexampleExists :=
  ⟨PaperConstruction.domain, PaperConstruction.paperConclusion⟩

end UnconditionalCounterexample
