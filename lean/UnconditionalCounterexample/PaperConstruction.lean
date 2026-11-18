import UnconditionalCounterexample.StageRecursion
import UnconditionalCounterexample.PrimaryTargets
import UnconditionalCounterexample.ReturnPrefix

/-!
# The simultaneous construction used in the manuscript

At each raw stage use the actual primary column of its normalized generator.
At the processed primary and guard of a q-stage the return target uses the
earlier polynomials of this very prefix. The recursion then fixes one sequence
of polynomials, exponents, and guards, hence one subring of ℚ(t).
-/

noncomputable section

namespace UnconditionalCounterexample.PaperConstruction

open Polynomial CombinedGuardStep StageRecursion RecursivePrefix PrimaryTargets

def targets {n : ℕ} (P : Prefix n) (B : Batch) : Targets B where
  value i b := P.generatorTarget (generatorAt n) (B.primeAt i) (B.branch i b)
    (B.branch_transcendental i b) (branchOrder n i.val b)
  precision i b := P.generatorPrecision (generatorAt n) (B.primeAt i) (B.branch i b)
    (B.branch_transcendental i b) (branchOrder n i.val b)
  nonzero i b := P.generatorTarget_ne_zero (generatorAt n) (B.primeAt i) (B.branch i b)
    (B.branch_transcendental i b) (branchOrder n i.val b)

theorem target_norm {n : ℕ} (P : Prefix n) (B : Batch) (i : B.indices) (b : Bool) :
    ‖(targets P B).value i b‖ = (B.primeAt i : ℝ) ^ (-(branchOrder n i.val b : ℤ)) :=
  P.generatorTarget_norm _ _ _ _ _

def requirements : Requirements where
  needed := requiredPrimes
  targets := targets

def construction : Sequence requirements := sequence requirements

abbrev raw := construction.chain.raw
abbrev exponent := construction.chain.exponent
abbrev places := construction.chain.guardChain.places
abbrev poles : Set ℚ[X] := Set.range raw
abbrev domain : Subring (RatFunc ℚ) := PairedDomain.domain poles places

theorem raw_constant {f : ℚ[X]} (hf : f ∈ poles) : constantCoeff f ≠ 0 := by
  obtain ⟨j, rfl⟩ := hf
  exact construction.chain.raw_constant_ne_zero j

theorem fractionRing : IsFractionRing domain (RatFunc ℚ) :=
  PairedDomain.fractionRing poles places

theorem integerLocalization :
    IsLocalization (IntersectionDomain.integerDenominators domain) (PoleAlgebra.generated poles) :=
  construction.chain.guardChain.integerLocalization (fun _ => raw_constant)

theorem rational_mem_iff_integer (q : ℚ) :
    (q : RatFunc ℚ) ∈ domain ↔ ∃ z : ℤ, (z : ℚ) = q :=
  PairedDomain.rational_mem_iff_integer poles places q

theorem guardSupport (f : RatFunc ℚ) (hf : f ≠ 0) :
    {p : GuardSupport.PrimeIndex | PairedDomain.vertical places (.inr p) f ≠ 1}.Finite :=
  construction.chain.guardChain.ratFunc_guardSupport_finite f hf

end UnconditionalCounterexample.PaperConstruction
