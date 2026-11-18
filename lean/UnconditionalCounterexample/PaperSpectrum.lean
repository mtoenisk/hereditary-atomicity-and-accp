import UnconditionalCounterexample.PaperValuations
import UnconditionalCounterexample.PairedSpectrum
import UnconditionalCounterexample.Target

/-!
# The concrete constructed domain is almost Dedekind

The single domain fixed by `PaperConstruction` has every maximal localization
an actual DVR. Its already proved integer localization and elementary generator
columns supply all inputs of the vertical/horizontal spectrum argument.
-/

noncomputable section
namespace UnconditionalCounterexample.PaperConstruction
open IntersectionDomain IntersectionStalks

local instance spectrumRatAlgebra : Algebra ℚ (RatFunc ℚ) := RatFunc.instAlgebraOfPolynomial ℚ ℚ

/-- Every maximal localization of the fixed constructed domain is a DVR. -/
theorem isAlmostDedekindDomain : IsAlmostDedekindDomain domain := by
  intro M _
  have hnonzero : ∀ f ∈ poles, f ≠ 0 := by
    intro f hf hz
    exact raw_constant hf (by simp [hz])
  let := fractionRing
  let := integerLocalization
  let := IntersectionSpectrum.poleAlgebra_isDedekindDomain poles hnonzero
  apply IntersectionSpectrum.every_maximal_stalk_isDVR
    (PoleAlgebra.generated poles).toSubring (PairedDomain.vertical places)
    (fun p => .inl (places.primes.symm p)) (fun p => .inr p)
    (PairedSpectrum.center_isMaximal poles places) (PairedSpectrum.vertical_isDVR places)
    (PairedSpectrum.paired_radicals raw exponent places
      generatorProfiles.b generatorProfiles.q generatorProfiles.guard) _ M
  intro i
  obtain ⟨f, hfinv, hfi, hfother⟩ := PairedSpectrum.vertical_isolators raw exponent places
    generatorProfiles.b generatorProfiles.q generatorProfiles.guard i
  exact ⟨f, 3, by decide, hfinv, hfi, hfother⟩

end UnconditionalCounterexample.PaperConstruction
