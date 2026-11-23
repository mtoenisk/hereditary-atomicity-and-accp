import UnconditionalCounterexample.Variations.MultiDomainAtomicity
import UnconditionalCounterexample.Variations.MultiDomainSelectedConductor

/-!
# The two boundary cases of prescribed dimension

For each positive number of variables, the ordinary and point-pullback
examples realize that dimension and its successor in the same rational
function field. Each has a strict chain starting at the first coordinate cubed.
-/

noncomputable section
namespace UnconditionalCounterexample.Variations

open MultivariateSelection MultiDomain

/-- Dimension equal to the number of variables. -/
theorem ordinaryDimensionDomain_spec (r : ℕ) : PrescribedDimension (ordinaryDimensionDomain r) (r+1) :=
  ordinaryDimensionDomain_of_conductor r (ordinary_integer_conductor r reservedPrime)

/-- Dimension one greater than the number of variables. -/
theorem upperDimensionDomain_spec (r : ℕ) : PrescribedDimension (upperDimensionDomain r) (r+2) :=
  upperDimensionDomain_of_conductor r (pullback_integer_conductor r reservedPrime)

end UnconditionalCounterexample.Variations
