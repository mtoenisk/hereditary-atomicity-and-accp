import UnconditionalCounterexample.Hierarchy.PrescribedRealization
import UnconditionalCounterexample.Hierarchy.PrescribedFactorizations
import UnconditionalCounterexample.Hierarchy.PrescribedFactorizationBounds
import UnconditionalCounterexample.Hierarchy.StrictClasses

/-! # The two prescribed-length separations among almost Dedekind overrings -/

namespace UnconditionalCounterexample.Hierarchy.Prescribed

open Factorization StrictHierarchy

/-- The binary-row ring has bounded factorization but fails finite factorization. -/
theorem binaryWitness :
    Witness (fun R => IsFFDomain R) (fun R => IsBFDomain R) binaryRing := by
  let G := generators (fun _ => 0) distinguishedPrime
  exact ⟨⟨intZ_le_ring _ _ G.poles, ring_isAlmostDedekind _ _ G.poles, G.binary_domain_bf⟩,
    G.not_isFFDomain⟩

/-- In this very ring, 2 has infinitely many distinct factorizations of length 2. -/
theorem binary_two_factorizations :
    {s ∈ atomicFactorizationClasses (2 : binaryRing) | s.card = 2}.Infinite :=
  (generators (fun _ => 0) distinguishedPrime).binary_infinite_length_two

/-- The ring with rows of growing size has ACCP and fails bounded factorization. -/
theorem unboundedWitness :
    Witness (fun R => IsBFDomain R) (fun R => WfDvdMonoid R) unboundedRing := by
  let G := generators id distinguishedPrime
  exact ⟨⟨intZ_le_ring _ _ G.poles, ring_isAlmostDedekind _ _ G.poles, G.domain_accp⟩,
    G.growing_not_isBFDomain⟩

/-- Each integer n+2 is the length of an actual atom factorization of 2 in the growing-row ring. -/
theorem unbounded_two_lengths (n : ℕ) :
    n + 2 ∈ factorizationLengths (2 : unboundedRing) :=
  (generators id distinguishedPrime).row_mem_lengths n

end UnconditionalCounterexample.Hierarchy.Prescribed
