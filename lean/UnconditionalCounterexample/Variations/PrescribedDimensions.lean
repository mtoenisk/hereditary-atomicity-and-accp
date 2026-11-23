import UnconditionalCounterexample.Variations.MultiDomainConclusion
import UnconditionalCounterexample.Variations.PrivateGuardsConclusion
import UnconditionalCounterexample.Variations.DimensionTrdeg

/-!
# Prescribing dimension and the rational function field

In positive transcendence degree, the punctured, ordinary and point-pullback
constructions cover all the dimensions from one through one more than the
number of variables. The fraction-field assertion uses the inclusion of each
chosen subring in the same rational function field.
-/

noncomputable section
namespace UnconditionalCounterexample.Variations.PrescribedDimensions

/-- A named subring, using the appropriate construction for the requested dimension. -/
def domain (r d : ℕ) (hr : 1 ≤ r) (hd : 1 ≤ d) (_hbound : d ≤ r+1) : Subring (FunctionField r) :=
  match r with
  | 0 => False.elim (by omega)
  | n+1 =>
    if h : d < n+1 then lowerDimensionDomain n d hd h
    else if d = n+1 then ordinaryDimensionDomain n else upperDimensionDomain n

/-- Normality, exact dimension, hereditary atomicity, failure of ACCP and
absolute transcendence degree for a single named domain in the specified field. -/
theorem conclusion (r d : ℕ) (hr : 1 ≤ r) (hd : 1 ≤ d) (hbound : d ≤ r+1) :
    PrescribedDimension (domain r d hr hd hbound) d ∧
      Algebra.trdeg ℤ (domain r d hr hd hbound) = r := by
  have h : PrescribedDimension (domain r d hr hd hbound) d := by
    cases r with
    | zero => omega
    | succ n =>
      by_cases hlt : d < n+1
      · simpa [domain, hlt] using lowerDimensionDomain_spec n d hd hlt
      · by_cases he : d = n+1
        · subst d
          simpa [domain, hlt] using ordinaryDimensionDomain_spec n
        · have heq : d = n+2 := by omega
          subst d
          simpa [domain, hlt, he] using upperDimensionDomain_spec n
  let := h.1
  exact ⟨h,subring_trdeg_of_fractionRing r _⟩

/-- Existence form of the prescribed-dimension theorem. -/
theorem exists_domain (r d : ℕ) (hr : 1 ≤ r) (hd : 1 ≤ d) (hbound : d ≤ r+1) :
    ∃ D : Subring (FunctionField r), PrescribedDimension D d ∧ Algebra.trdeg ℤ D = r :=
  ⟨domain r d hr hd hbound, conclusion r d hr hd hbound⟩

end UnconditionalCounterexample.Variations.PrescribedDimensions
