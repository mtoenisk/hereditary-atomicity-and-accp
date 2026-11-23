import UnconditionalCounterexample.Variations.PrivateGuardsConclusion
import UnconditionalCounterexample.Variations.DimensionTrdeg

/-!
# The two-variable, one-dimensional punctured example

All statements use one specified joint sequence. The public table uses the
prime 2 as its reserved prime and the coordinate flag runs through the origin.
-/

noncomputable section
namespace UnconditionalCounterexample.Variations.PrivateGuards.PlaneClient

open MvPolynomial MultivariateSelection GuardSupport Live

def config : Config 1 1 := (config_exists (by decide) (by decide)).some

abbrev reserved := MultivariateSelection.reservedPrime

abbrev policy := genericTablePolicy 1 ℂ
abbrev origin : Fin 2 → ℚ := 0
abbrev choice := tableRule policy reserved origin
abbrev path := publicPath policy reserved origin config
abbrev pole := horizontal config choice
abbrev ring := tableDomain policy reserved origin config

theorem fractionField : IsFractionRing ring (FunctionField 2) :=
  tableDomain_fraction policy reserved origin config

theorem dimension : ringKrullDim ring = 1 := tableDomain_dimension policy reserved origin config

theorem transcendenceDegree : Algebra.trdeg ℤ ring = 2 := by
  let := fractionField
  exact subring_trdeg_of_fractionRing 2 ring

theorem normal : IsIntegrallyClosed ring := tableDomain_normal policy reserved origin config

/-- The actual embedded horizontal algebra has the prescribed smaller dimension. -/
theorem pole_dimension : ringKrullDim pole = 1 := by
  exact (family config choice).pole_dimension (fun n => (event config choice n).irreducible)

/-- The public primaries and all old private pairs receive the arithmetic targets of this example. -/
theorem processed (j n : ℕ) (hb : j/2 ≤ n) :
    let φ := (aeval (R := ℚ) ((path.places.primary j).x)).toRingHom
    φ (main config choice n) ∈ mixedSet (before config choice n) φ Padic.mulValuation (path.places.primes j).val (some j) :=
  processed_primary_mem policy reserved origin config j n hb

theorem private_return {j n : ℕ} (hj : j < n) (b : Bool) :
    let φ := (aeval (R := ℚ) ((event config choice j).pair.point b)).toRingHom
    φ (main config choice n) ∈ mixedSet (before config choice n) φ Padic.mulValuation (prime config choice j).val none :=
  processed_private_mem policy reserved origin config hj b

/-- Every rational subalgebra containing admissible words at arbitrarily late
stages equals this actual enlarged horizontal algebra. -/
theorem recover (A : Subalgebra ℚ pole) (hwords : {n | ∃ (w : BoundedWord n) (x : A),
    let W := (family config choice).generator mixedPower
    (((x : pole) : FractionRing (Poly 1))) = W n ^ w.latestExponent *
      (∏ j ∈ Finset.range n, W j ^ w.oldExponent j)}.Infinite) : A = ⊤ := by
  let : Uncountable ℂ := Set.not_countable_univ_iff.mp not_countable_complex
  exact genericTable_recover ℂ reserved origin config A hwords

/-- This same two-variable ring satisfies the full one-dimensional theorem. -/
theorem spec : PrescribedDimension ring 1 :=
  lowerDimensionDomain_spec 1 1 (by decide) (by decide)

theorem principal_chain : ∃ t : ring, (t : FunctionField 2) = MultiDomain.coordinate 0 ∧ HasStrictChainAt (t^3) :=
  lowerDimensionDomain_chain 1 1 (by decide) (by decide)

end UnconditionalCounterexample.Variations.PrivateGuards.PlaneClient
