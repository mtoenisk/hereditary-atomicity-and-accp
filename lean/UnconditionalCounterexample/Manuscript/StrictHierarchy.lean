import UnconditionalCounterexample.Hierarchy.EvaluationQuotient
import UnconditionalCounterexample.Hierarchy.StrictImplications

/-! # Strict factorization inclusions for almost Dedekind overrings of Int(ℤ) -/

namespace UnconditionalCounterexample.StrictHierarchy

open Factorization Hierarchy

/-- The binary-row ring has infinitely many factorizations of its rational
prime into two atoms and has bounded factorization. -/
theorem ffd_ssubset_bfd :
    rings (fun R => IsFFDomain R) ⊂ rings (fun R => IsBFDomain R) :=
  strictSubset_of_witness (fun _ => IsFFDomain.isBFDomain) Prescribed.binaryWitness

/-- The growing-row ring has ACCP, and its rational prime has unbounded
factorization lengths. -/
theorem bfd_ssubset_accp :
    rings (fun R => IsBFDomain R) ⊂ rings (fun R => WfDvdMonoid R) :=
  strictSubset_of_witness (fun _ => IsBFDomain.wfDvdMonoid) Prescribed.unboundedWitness

/-- The original constructed domain lies in the weak ACCP class and falls
outside the ACCP class. Its maximal localizations are DVRs. -/
theorem original_witness : Witness (fun R => WfDvdMonoid R) (fun R => IsWeakACCP R)
    PaperConstruction.domain := by
  obtain ⟨hInt, hDVR, hWeak, hchain⟩ := originalWeakACCPWitness
  exact ⟨⟨hInt, hDVR, hWeak⟩, hchain⟩

/-- ACCP gives a proper subclass of weak ACCP among almost Dedekind
overrings of the integer-valued polynomials in ℚ(t). -/
theorem accp_ssubset_weakACCP :
    rings (fun R => WfDvdMonoid R) ⊂ rings (fun R => IsWeakACCP R) :=
  strictSubset_of_witness (fun _ => isWeakACCP_of_wfDvdMonoid) original_witness

/-- The two-chain ring lies in the strongly atomic class and fails weak ACCP. -/
theorem weakACCP_ssubset_stronglyAtomic :
    rings (fun R => IsWeakACCP R) ⊂ rings (fun R => IsStronglyAtomicDomain R) :=
  strictSubset_of_witness (fun _ => IsWeakACCP.isStronglyAtomicDomain) twoChain_overring.1

/-- The dyadic ring lies in the atomic class and fails strong atomicity. -/
theorem stronglyAtomic_ssubset_atomic :
    rings (fun R => IsStronglyAtomicDomain R) ⊂ rings (fun R => IsAtomicDomain R) :=
  strictSubset_of_witness (fun _ => IsStronglyAtomicDomain.isAtomicDomain) dyadic_overring.1

/-- The marked-fiber ring is quasi-atomic and admits no atomic multiplier
for the element of weight one. -/
theorem almostAtomic_ssubset_quasiAtomic :
    rings (fun R => IsAlmostAtomicDomain R) ⊂ rings (fun R => IsQuasiAtomicDomain R) :=
  strictSubset_of_witness (fun _ => IsAlmostAtomicDomain.isQuasiAtomicDomain) Weighted.weightedWitness

end UnconditionalCounterexample.StrictHierarchy
