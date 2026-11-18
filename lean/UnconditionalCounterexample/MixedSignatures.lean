import UnconditionalCounterexample.MixedConstruction
import UnconditionalCounterexample.SparseResidues

/-!
# Counting the actual domains by their prime-index subrings

The family is indexed by all infinite sets of rational primes. Its intrinsic
signature identifies each index. Consequently its range is a set of continuum
many embedded domains, any two distinct members of which are nonisomorphic
even as abstract rings.
-/

noncomputable section
namespace UnconditionalCounterexample.MixedVariation
open GuardSupport PrimeIndexSignature

abbrev Parameter := {S : Set PrimeIndex // S.Infinite}

def family (s : Parameter) : Subring (RatFunc ℚ) := MixedConstruction.domain s.val s.property

theorem signature_family (s : Parameter) : signature (family s) = s.val :=
  SparseResidues.signature_eq_selected (MixedConstruction.poles s.val s.property) s.val s.property
    _ _ (fun p _ => (MixedConstruction.construction s.val s.property).chain.guardChain.value_unit p)

theorem family_nonisomorphic {s t : Parameter} (h : s ≠ t) :
    ¬ Nonempty (family s ≃+* family t) :=
  not_ringEquiv_of_distinct_signatures (signature_family s) (signature_family t)
    (fun he => h (Subtype.ext he))

theorem family_injective : Function.Injective family := by
  intro s t h
  apply Subtype.ext
  rw [← signature_family s, ← signature_family t, h]

theorem cardinal_range : Cardinal.mk (Set.range family) = Cardinal.continuum :=
  (Cardinal.mk_congr (Equiv.ofInjective family family_injective)).symm.trans
    cardinal_infinite_prime_sets

theorem range_nonisomorphic {D E : Subring (RatFunc ℚ)}
    (hD : D ∈ Set.range family) (hE : E ∈ Set.range family) (hne : D ≠ E) :
    ¬ Nonempty (D ≃+* E) := by
  obtain ⟨s, rfl⟩ := hD
  obtain ⟨t, rfl⟩ := hE
  exact family_nonisomorphic (fun h => hne (congrArg family h))

end UnconditionalCounterexample.MixedVariation
