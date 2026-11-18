import HereditaryAtomicity.DVRBase.SemilocalBlockInput
import HereditaryAtomicity.DVRBase.SemilocalConclusion
import HereditaryAtomicity.DVRBase.SourceCertificate

/-!
# Every semilocal hereditarily atomic domain is hereditarily ACCP

Failure at an actual maximal stalk produces the original-source chain and
its canonical completed block input. The constructed source certificate is
then pulled back to the original domain by the selected source ratios and
scaled endpoints. Hereditary atomicity is used only in the original domain.
-/

noncomputable section
universe u
namespace HereditaryAtomicity.DVRBase
open scoped NNReal

namespace SemilocalChainSetup
variable {K : Type*} [Field K] {D : Subring K} [IsFractionRing D K]
  {M : MaximalSpectrum D} (H : SemilocalChainSetup D M)

include H

/-- The actual source chain at a failed stalk contradicts original-domain
hereditary atomicity. All moving-basis, kernel and source-certificate inputs
are constructed by the canonical completion factory. -/
theorem not_hereditarilyAtomic : ¬ Factorization.IsHereditarilyAtomic D := by
  let := H.completedBaseNorm
  let := H.completedAlgebra
  let : IsDiscreteValuationRing H.base := H.base_dvr
  obtain ⟨Λ, _, _, hcofinal, hno, _⟩ :=
    H.completedBlockInput.exists_source_certificate H.valuation
      H.completedBlockInput_source_valuation H.completedBlockInput_order
      H.base H.base_le H.uniformizer H.uniformizer_irreducible rfl H.base_bounded
      (completionValuation H.fractionValuation) (fun _ => rfl)
      (algebraMap (FractionRing H.base) (ValuationNormCompletion H.fractionValuation))
      H.coefficient_completion_valuation
      (algebraMap K (ValuationNormCompletion H.valuation)) (fun _ => rfl)
      H.completed_coefficient_square
  exact H.not_hereditarilyAtomic_of_selected_certificate H.completedBlockInput
    BlockState.basisLoss H.completedBlockInput_chain
    H.completedBlockInput_source_valuation Λ hcofinal hno

end SemilocalChainSetup

/-- ACCP at every actual maximal stalk of an embedded nonfield semilocal HA
domain, with no hereditary-atomicity hypothesis on the localization. -/
theorem embedded_semilocal_ha_wfDvdMonoid_atPrime
    {K : Type u} [Field K] (D : Subring K) [IsFractionRing D K]
    [Finite (MaximalSpectrum D)] (hD : Factorization.IsHereditarilyAtomic D)
    (hfield : ¬ IsField D) (M : MaximalSpectrum D) :
    WfDvdMonoid (Localization.AtPrime M.asIdeal) := by
  by_contra hfail
  obtain ⟨H⟩ := exists_semilocalChainSetup D hD hfield M hfail
  exact H.not_hereditarilyAtomic hD

/-- Every actual maximal localization of any semilocal HA domain satisfies
ACCP. This includes fields and does not depend on an ambient-field choice. -/
theorem semilocal_ha_wfDvdMonoid_atPrime
    {R : Type u} [CommRing R] [IsDomain R] [Finite (MaximalSpectrum R)]
    (hR : Factorization.IsHereditarilyAtomic R) (M : MaximalSpectrum R) :
    WfDvdMonoid (Localization.AtPrime M.asIdeal) :=
  maximal_stalks_of_embedded_source_result
    (fun _ _ _ _ _ => embedded_semilocal_ha_wfDvdMonoid_atPrime _) hR M

/-- A semilocal hereditarily atomic domain satisfies ACCP. -/
theorem semilocal_ha_wfDvdMonoid
    {R : Type u} [CommRing R] [IsDomain R] [Finite (MaximalSpectrum R)]
    (hR : Factorization.IsHereditarilyAtomic R) : WfDvdMonoid R :=
  wfDvdMonoid_of_maximal_localizations (semilocal_ha_wfDvdMonoid_atPrime hR)

/-- Every unital subring of a semilocal hereditarily atomic domain satisfies
ACCP, with intrinsic units and divisibility in that subring. -/
theorem semilocal_ha_hereditarilyACCP
    {R : Type u} [CommRing R] [IsDomain R] [Finite (MaximalSpectrum R)]
    (hR : Factorization.IsHereditarilyAtomic R) : Factorization.IsHereditarilyACCP R :=
  hereditarilyACCP_of_maximal_localizations hR (semilocal_ha_wfDvdMonoid_atPrime hR)

end HereditaryAtomicity.DVRBase
