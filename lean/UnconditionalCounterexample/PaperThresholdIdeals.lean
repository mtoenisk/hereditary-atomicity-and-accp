import UnconditionalCounterexample.PaperThresholdProfiles
import UnconditionalCounterexample.PaperIdealProfiles
import UnconditionalCounterexample.PaperStalkOrders
import UnconditionalCounterexample.IntegralIdealProfiles

/-!
# Actual integral threshold ideals from realized fractional profiles

This is the final conversion between the ideal-profile realization and the
arbitrary-ideal SP argument: nonnegative realized threshold coordinates give
an actual integral ideal, and the already proved maximal-order dictionary
identifies its exact local indicator ideals.
-/

noncomputable section
namespace UnconditionalCounterexample.PaperThresholdIdeals
open WithZero PaperConstruction PicardProfiles FractionalIdealProfiles
open PaperMaximalSpectrum RadicalIdealProducts
open scoped nonZeroDivisors BigOperators
local instance : Algebra ℚ (RatFunc ℚ) := RatFunc.instAlgebraOfPolynomial ℚ ℚ
local instance : IsFractionRing domain (RatFunc ℚ) := fractionRing

/-- The all-maximal natural order is the exponent of the actual valuation. -/
theorem value_at_maximal (M : PaperMaximalSpectrum.Maximal) (x : domain) (hx : x ≠ 0) :
    PaperIdealProfiles.v (labelEquivMaximal.symm M) (algebraMap domain (RatFunc ℚ) x) =
      exp (-(PaperMaximalSpectrum.order M x : ℤ)) := by
  change CompleteProfiles.valuations poles places (labelEquivMaximal.symm M) (x : RatFunc ℚ) = _
  rw [DiscreteOrders.value_eq_exp_neg_order _ (fun h => hx (Subtype.ext h)),
    ← valuationProfiles_cast _ x hx]
  rfl

/-- A realized fractional threshold profile produces the exact ordinary
threshold ideal required by the direct arbitrary-ideal SP proof. -/
theorem exists_integral_threshold (x : domain) (hx : x ≠ 0) (k : ℕ) (hk : 0 < k)
    (I : PaperIdealProfiles.Fractional)
    (hI : HasProfile PaperIdealProfiles.v I (coordinate (thresholdProfile x hx k hk))) :
    ∃ J : Ideal domain, ∀ M : PaperMaximalSpectrum.Maximal,
      localIdeal M J = if k ≤ PaperMaximalSpectrum.order M x then localMaximal M else ⊤ := by
  obtain ⟨J, hJ⟩ := IntegralIdealProfiles.exists_integral_ideal PaperIdealProfiles.v
    PaperIdealProfiles.full I _ hI (thresholdProfile_nonneg x hx k hk)
  refine ⟨J, fun M => ?_⟩
  have hv := hI (labelEquivMaximal.symm M)
  rw [← hJ, thresholdProfile_coordinate] at hv
  let n : ℕ := if k ≤ PaperMaximalSpectrum.order M x then 1 else 0
  have hvn : HasValue (J : PaperIdealProfiles.Fractional)
      (PaperIdealProfiles.v (labelEquivMaximal.symm M)) (n : ℤ) := by
    change HasValue (J : PaperIdealProfiles.Fractional)
      (PaperIdealProfiles.v (labelEquivMaximal.symm M))
      (if k ≤ PaperMaximalSpectrum.order M x then 1 else 0) at hv
    by_cases h : k ≤ PaperMaximalSpectrum.order M x <;> simpa [n, h] using hv
  have h := IntegralIdealProfiles.localIdeal_eq_pow_of_hasValue
    (fun M => PaperIdealProfiles.v (labelEquivMaximal.symm M)) PaperMaximalSpectrum.order
    value_at_maximal principal_power J M n hvn
  simpa [n, Ideal.one_eq_top] using h

/-- The actual domain's arbitrary-ideal factorization is reduced solely to
realizing its positive threshold tuples; all spectrum and normalization inputs
have already been proved for this fixed construction. -/
theorem radical_products_of_threshold_realizations
    (hrealize : ∀ (x : domain) (hx : x ≠ 0) (k : ℕ) (hk : 0 < k),
      ∃ I : PaperIdealProfiles.Fractional,
        HasProfile PaperIdealProfiles.v I (coordinate (thresholdProfile x hx k hk)))
    (J : Ideal domain) :
    ∃ N : ℕ, ∃ K : ℕ → Ideal domain, (∀ k, (K k).IsRadical) ∧
      J = ∏ k ∈ Finset.range N, K k := by
  apply RadicalIdealProducts.every_ideal_radical_product PaperMaximalSpectrum.order
    principal_power order_bounded _ J
  intro x hx k hk
  obtain ⟨I, hI⟩ := hrealize x hx k hk
  exact exists_integral_threshold x hx k hk I hI

end UnconditionalCounterexample.PaperThresholdIdeals
