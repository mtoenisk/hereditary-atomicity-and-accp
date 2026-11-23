import Factorization.StrictHierarchy
import UnconditionalCounterexample.Hierarchy.IntegerValued
import UnconditionalCounterexample.RationalFunctionSubring
import UnconditionalCounterexample.Target

/-!
# Factorization classes of almost Dedekind overrings of Int(ℤ)

Every strict inclusion compares properties of subrings of the same field.
The witness for an adjacent pair records both ambient conditions on the
particular ring furnishing the separation.
-/

namespace UnconditionalCounterexample.StrictHierarchy

open Factorization Hierarchy

/-- Almost Dedekind overrings of Int(ℤ) inside ℚ(t) satisfying `P`. -/
def rings (P : Subring (RatFunc ℚ) → Prop) : Set (Subring (RatFunc ℚ)) :=
  {R | intZInK ≤ R ∧ IsAlmostDedekindDomain R ∧ P R}

/-- Every ring in the hierarchy has fraction field ℚ(t) under inclusion. -/
theorem fractionRing_of_mem {P : Subring (RatFunc ℚ) → Prop} {R : Subring (RatFunc ℚ)}
    (h : R ∈ rings P) : IsFractionRing R (RatFunc ℚ) := by
  apply RationalFunctionSubring.isFractionRing_of_X_mem R (h.1 ?_)
  refine ⟨Polynomial.X, (mem_intZPolynomials_iff _).mpr ?_, RatFunc.algebraMap_X⟩
  exact fun z => ⟨z, by simp⟩

/-- A specified ring in the weaker class that fails the stronger property. -/
def Witness (P Q : Subring (RatFunc ℚ) → Prop) (R : Subring (RatFunc ℚ)) : Prop :=
  R ∈ rings Q ∧ ¬ P R

/-- A uniform forward implication and one witness give a strict inclusion. -/
theorem strictSubset_of_witness {P Q : Subring (RatFunc ℚ) → Prop}
    (forward : ∀ R, P R → Q R) {R : Subring (RatFunc ℚ)} (h : Witness P Q R) :
    rings P ⊂ rings Q := by
  have hPQ : rings P ⊆ rings Q := fun S hS => ⟨hS.1, hS.2.1, forward S hS.2.2⟩
  apply (Set.ssubset_iff_of_subset hPQ).mpr
  exact ⟨R, h.1, fun hR => h.2 hR.2.2⟩

/-- Assemble seven same-ring witnesses using the forward implications for
arbitrary domains. Each existence claim is supplied by the corresponding
witness proof. -/
theorem strictInclusions_of_witnesses {Rbf Raccp Rweak Rstrong Ratomic Ralmost Rquasi :
    Subring (RatFunc ℚ)}
    (hbf : Witness (fun R => IsFFDomain R) (fun R => IsBFDomain R) Rbf)
    (haccp : Witness (fun R => IsBFDomain R) (fun R => WfDvdMonoid R) Raccp)
    (hweak : Witness (fun R => WfDvdMonoid R) (fun R => IsWeakACCP R) Rweak)
    (hstrong : Witness (fun R => IsWeakACCP R) (fun R => IsStronglyAtomicDomain R) Rstrong)
    (hatomic : Witness (fun R => IsStronglyAtomicDomain R) (fun R => IsAtomicDomain R) Ratomic)
    (halmost : Witness (fun R => IsAtomicDomain R) (fun R => IsAlmostAtomicDomain R) Ralmost)
    (hquasi : Witness (fun R => IsAlmostAtomicDomain R) (fun R => IsQuasiAtomicDomain R) Rquasi) :
    (rings (fun R => IsFFDomain R) ⊂ rings (fun R => IsBFDomain R)) ∧
    (rings (fun R => IsBFDomain R) ⊂ rings (fun R => WfDvdMonoid R)) ∧
    (rings (fun R => WfDvdMonoid R) ⊂ rings (fun R => IsWeakACCP R)) ∧
    (rings (fun R => IsWeakACCP R) ⊂ rings (fun R => IsStronglyAtomicDomain R)) ∧
    (rings (fun R => IsStronglyAtomicDomain R) ⊂ rings (fun R => IsAtomicDomain R)) ∧
    (rings (fun R => IsAtomicDomain R) ⊂ rings (fun R => IsAlmostAtomicDomain R)) ∧
    (rings (fun R => IsAlmostAtomicDomain R) ⊂ rings (fun R => IsQuasiAtomicDomain R)) :=
  ⟨strictSubset_of_witness (fun _ => IsFFDomain.isBFDomain) hbf,
   strictSubset_of_witness (fun _ => IsBFDomain.wfDvdMonoid) haccp,
   strictSubset_of_witness (fun _ => isWeakACCP_of_wfDvdMonoid) hweak,
   strictSubset_of_witness (fun _ => IsWeakACCP.isStronglyAtomicDomain) hstrong,
   strictSubset_of_witness (fun _ => IsStronglyAtomicDomain.isAtomicDomain) hatomic,
   strictSubset_of_witness (fun _ => IsAtomicDomain.isAlmostAtomicDomain) halmost,
   strictSubset_of_witness (fun _ => IsAlmostAtomicDomain.isQuasiAtomicDomain) hquasi⟩

end UnconditionalCounterexample.StrictHierarchy
