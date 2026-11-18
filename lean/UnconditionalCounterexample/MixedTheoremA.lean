import UnconditionalCounterexample.MixedAtomicity
import UnconditionalCounterexample.MixedSquareChainActual
import UnconditionalCounterexample.MixedSP
import UnconditionalCounterexample.MixedPicard

/-! Every infinite selected prime set gives the literal Theorem A properties
on one actual domain. The parameter and square chain use that same domain. -/

namespace UnconditionalCounterexample.MixedConstruction
open GuardSupport
variable (S : Set PrimeIndex) (hS : S.Infinite)

theorem atom_zero_eq_parameter : atom S hS 0 = parameter S hS := Subtype.ext rfl

theorem parameter_irreducible : Irreducible (parameter S hS) :=
  atom_zero_eq_parameter S hS ▸ atom_irreducible S hS 0

/-- The full literal Theorem A conclusion for every infinite selected set. -/
theorem theoremAConclusion : PaperTargets.TheoremAConclusion (domain S hS) :=
  ⟨hereditarilyAtomic S hS, fractionRing S hS, isUnit_iff_sign S hS,
    ⟨parameter S hS, rfl, parameter_irreducible S hS, squareChainConclusion S hS⟩,
    not_wfDvdMonoid S hS, isAlmostDedekindDomain S hS, isSPDomain S hS,
    picardGroupConclusion S hS⟩

end UnconditionalCounterexample.MixedConstruction
