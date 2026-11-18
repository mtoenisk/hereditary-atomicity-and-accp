import Factorization.Hereditary
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Spectrum.Maximal.Basic
import Mathlib.RingTheory.Ideal.Maps

/-!
# The literal image of a domain in its fraction field

These adapters let statements about embedded subrings apply to arbitrary domains
with a specified fraction field, using the actual algebra map and its range.
-/

namespace HereditaryAtomicity

/-- Finiteness of the maximal spectrum transports along a ring equivalence. -/
theorem finite_maximalSpectrum_of_ringEquiv {A B : Type*} [CommRing A] [CommRing B]
    [Finite (MaximalSpectrum A)] (e : A ≃+* B) : Finite (MaximalSpectrum B) := by
  let f : MaximalSpectrum B → MaximalSpectrum A := fun M =>
    ⟨M.asIdeal.comap e.toRingHom, Ideal.comap_isMaximal_of_equiv e⟩
  apply Finite.of_injective f
  intro M N h
  apply MaximalSpectrum.ext
  exact Ideal.comap_injective_of_surjective e.toRingHom e.surjective
    (congrArg MaximalSpectrum.asIdeal h)

variable (R K : Type*) [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]

/-- The canonical equivalence onto the actual fraction-field image. -/
noncomputable def fractionImageEquiv : R ≃+* (algebraMap R K).range :=
  RingEquiv.ofBijective (algebraMap R K).rangeRestrict
    ⟨fun _ _ h => IsFractionRing.injective R K (congrArg Subtype.val h),
      (algebraMap R K).rangeRestrict_surjective⟩

omit [IsDomain R] in
@[simp]
theorem fractionImageEquiv_coe (r : R) :
    ((fractionImageEquiv R K r : (algebraMap R K).range) : K) = algebraMap R K r := rfl

omit [IsDomain R] in
/-- The literal image has the same full ambient fraction field. -/
theorem isFractionRing_fractionImage : IsFractionRing (algebraMap R K).range K := by
  apply IsFractionRing.of_ringEquiv_left (fractionImageEquiv R K).symm
  intro x
  have h := congrArg (fun a : (algebraMap R K).range => (a : K))
    ((fractionImageEquiv R K).apply_symm_apply x)
  exact h.symm

/-- HA transfers to the actual fraction-field image, with intrinsic subrings. -/
theorem hereditarilyAtomic_fractionImage (hR : Factorization.IsHereditarilyAtomic R) :
    Factorization.IsHereditarilyAtomic (algebraMap R K).range :=
  (Factorization.isHereditarilyAtomic_ringEquiv_iff (fractionImageEquiv R K)).mpr hR

omit [IsDomain R] in
/-- Semilocality is unchanged by passing to the actual fraction-field image. -/
theorem finite_maximalSpectrum_fractionImage [Finite (MaximalSpectrum R)] :
    Finite (MaximalSpectrum (algebraMap R K).range) :=
  finite_maximalSpectrum_of_ringEquiv (fractionImageEquiv R K)

end HereditaryAtomicity
