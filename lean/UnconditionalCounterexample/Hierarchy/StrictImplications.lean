import UnconditionalCounterexample.Hierarchy.PrescribedWitnesses
import UnconditionalCounterexample.Hierarchy.Original
import UnconditionalCounterexample.Hierarchy.UnivariateOverrings
import UnconditionalCounterexample.Hierarchy.AlmostAtomicPolynomial
import UnconditionalCounterexample.Hierarchy.WeightedSeparation

/-! # Seven strict inclusions among almost Dedekind overrings of Int(ℤ) in ℚ(t) -/

namespace UnconditionalCounterexample.StrictHierarchy

open Factorization Hierarchy

/-- Every adjacent factorization implication from FFD to quasi-atomicity is
strict in the class of almost Dedekind overrings of the integer-valued polynomials. -/
theorem strictInclusions :
    (rings (fun R => IsFFDomain R) ⊂ rings (fun R => IsBFDomain R)) ∧
    (rings (fun R => IsBFDomain R) ⊂ rings (fun R => WfDvdMonoid R)) ∧
    (rings (fun R => WfDvdMonoid R) ⊂ rings (fun R => IsWeakACCP R)) ∧
    (rings (fun R => IsWeakACCP R) ⊂ rings (fun R => IsStronglyAtomicDomain R)) ∧
    (rings (fun R => IsStronglyAtomicDomain R) ⊂ rings (fun R => IsAtomicDomain R)) ∧
    (rings (fun R => IsAtomicDomain R) ⊂ rings (fun R => IsAlmostAtomicDomain R)) ∧
    (rings (fun R => IsAlmostAtomicDomain R) ⊂ rings (fun R => IsQuasiAtomicDomain R)) := by
  obtain ⟨hInt,hDVR,hWeak,hACC⟩ := originalWeakACCPWitness
  exact strictInclusions_of_witnesses Prescribed.binaryWitness Prescribed.unboundedWitness
    (Rweak := PaperConstruction.domain) ⟨⟨hInt,hDVR,hWeak⟩,hACC⟩
    twoChain_overring.1 dyadic_overring.1 AlmostAtomicPolynomial.witness Weighted.weightedWitness

end UnconditionalCounterexample.StrictHierarchy
