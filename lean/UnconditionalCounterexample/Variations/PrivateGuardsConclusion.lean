import UnconditionalCounterexample.Variations.PrivateGuardsAtomicity
import UnconditionalCounterexample.Variations.PrivateGuardsConductor
import UnconditionalCounterexample.Variations.PrivateGuardsTableProfiles
import UnconditionalCounterexample.Variations.PrivateTableDimension
import UnconditionalCounterexample.Variations.MultiDomainExamples
import Mathlib.Analysis.Complex.Cardinality
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Every lower dimension in the rational function field

For each positive dimension below the number of variables, the punctured
domain is normal, has the full fraction field, is hereditarily atomic, and
has a strict principal-ideal chain starting at the first coordinate cubed.
-/

noncomputable section
namespace UnconditionalCounterexample.Variations

open PrivateGuards.Live MultivariateSelection MultiDomain GuardSupport WithZero

def lowerDimensionDomain (n d : ℕ) (hd : 1 ≤ d) (hlt : d < n+1) : Subring (FunctionField (n+1)) :=
  tableDomain (genericTablePolicy n ℂ) reservedPrime 0 (config_exists hd hlt).some

theorem lowerDimensionDomain_chain (n d : ℕ) (hd : 1 ≤ d) (hlt : d < n+1) :
    ∃ t : lowerDimensionDomain n d hd hlt, (t : FunctionField (n+1)) = coordinate 0 ∧ HasStrictChainAt (t^3) := by
  let P := genericTablePolicy n ℂ
  let C := (config_exists hd hlt).some
  exact cube_chain C (tableRule P reservedPrime 0) _ _ (actualMovingValues P reservedPrime 0 C)

/-- The full joint specification on the selected lower-dimensional ring. -/
theorem lowerDimensionDomain_spec (n d : ℕ) (hd : 1 ≤ d) (hlt : d < n+1) :
    PrescribedDimension (lowerDimensionDomain n d hd hlt) d := by
  let : Uncountable ℂ := Set.not_countable_univ_iff.mp not_countable_complex
  let P := genericTablePolicy n ℂ
  let q := reservedPrime
  let c := (0 : Fin (n+1) → ℚ)
  let C := (config_exists hd hlt).some
  let L := tableRule P q c
  let T := publicPath P q c C
  let H := actualProfileValues P q c C
  obtain ⟨_,_,hchain⟩ := lowerDimensionDomain_chain n d hd hlt
  refine ⟨tableDomain_fraction P q c C,tableDomain_normal P q c C,tableDomain_dimension P q c C,
    H.hereditarilyAtomic ?_ (integer_conductor_of_mixed_words ℂ q c C),not_wf_of_strict_chain hchain⟩
  apply integer_return C L (publicPrimary P q c C) (publicGuard P q c C) T.places.primes T.places.injective H.toMovingValues
  · apply branch_prime_value
    · intro j
      exact EvaluationDVR.valuation_prime (T.places.primes j).val
        (IndependentTuples.evaluation (T.places.primary j).x (T.places.primary j).independent)
    · intro p
      exact ((T.places.guard p).valuation_natCast _).trans (T.places.guard_prime p)
  · exact actualBranchReturn P q c C

end UnconditionalCounterexample.Variations
