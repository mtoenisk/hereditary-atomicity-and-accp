import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Localization.Integer
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.IntegralClosure.IntegralRestrict
import Mathlib.RingTheory.QuasiFinite.Basic
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Spectrum.Maximal.Basic
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.Localization.AsSubring
import Mathlib.RingTheory.Localization.Integral

/-!
# Finite birational algebras and normalization

Finite generation in the actual fraction field supplies a common nonzero
conductor denominator. The argument applies to any finite intermediate algebra,
not only the entire normalization.
-/

namespace HereditaryAtomicity

universe u v

/-- Every finite intermediate algebra in the actual fraction field has a
nonzero conductor into the source. -/
theorem exists_nonzero_conductor_of_finite_subalgebra
    (R : Type u) [CommRing R] [IsDomain R] (K : Type v) [Field K]
    [Algebra R K] [IsFractionRing R K] (E : Subalgebra R K) [Module.Finite R E] :
    ∃ c : R, c ≠ 0 ∧ ∀ x : E, ∃ r : R,
      algebraMap R K r = algebraMap R K c * (x : K) := by
  classical
  obtain ⟨s, hs⟩ := (Module.finite_def.mp (inferInstance : Module.Finite R E))
  obtain ⟨c, hc⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors R)
    s (fun x : E => (x : K))
  refine ⟨c, nonZeroDivisors.coe_ne_zero c, ?_⟩
  intro x
  have hx : x ∈ Submodule.span R (s : Set E) := by rw [hs]; trivial
  have hint : IsLocalization.IsInteger R ((c : R) • (x : K)) := by
    induction hx using Submodule.span_induction with
    | mem x hx => exact hc x hx
    | zero => simpa using (IsLocalization.isInteger_zero (R := R) (S := K))
    | add x y _ _ hx hy => simpa [smul_add] using IsLocalization.isInteger_add hx hy
    | smul a x _ hx =>
      simpa only [Subalgebra.coe_smul, smul_comm (c : R) a (x : K)] using
        IsLocalization.isInteger_smul (a := a) hx
  obtain ⟨r, hr⟩ := hint
  exact ⟨r, by simpa only [Algebra.smul_def] using hr⟩

/-- A module-finite algebra over a semilocal ring is semilocal. -/
theorem finite_maximalSpectrum_of_moduleFinite
    (R : Type u) [CommRing R] (S : Type v) [CommRing S]
    [Algebra R S] [Module.Finite R S] [Finite (MaximalSpectrum R)] :
    Finite (MaximalSpectrum S) := by
  classical
  let maxima : Set (PrimeSpectrum R) := Set.range MaximalSpectrum.toPrimeSpectrum
  have hmaxima : maxima.Finite := Set.finite_range _
  have hpreimage := Algebra.QuasiFinite.finite_comap_preimage (R := R) (S := S) hmaxima
  let F := {P : PrimeSpectrum S // PrimeSpectrum.comap (algebraMap R S) P ∈ maxima}
  let : Fintype F := hpreimage.fintype
  let f : MaximalSpectrum S → F := fun Q =>
    ⟨Q.toPrimeSpectrum, ⟨⟨Q.asIdeal.under R,
      Ideal.isMaximal_under_of_isIntegral_of_isMaximal Q.asIdeal⟩, rfl⟩⟩
  exact Finite.of_injective f (fun Q Q' h =>
    MaximalSpectrum.toPrimeSpectrum_injective (congrArg Subtype.val h))

/-- Module-finite normalization supplies a nonzero source conductor element. -/
theorem normalization_has_nonzero_conductor_of_finite
    (R : Type u) [CommRing R] [IsDomain R] (K : Type v) [Field K]
    [Algebra R K] [IsFractionRing R K] [Module.Finite R (integralClosure R K)] :
    ∃ c : R, c ≠ 0 ∧ ∀ x : integralClosure R K, ∃ r : R,
      algebraMap R K r = algebraMap R K c * (x : K) :=
  exists_nonzero_conductor_of_finite_subalgebra R K (integralClosure R K)

/-- Module-finite normalization is semilocal when its source is semilocal. -/
theorem finite_maximalSpectrum_normalization_of_finite
    (R : Type u) [CommRing R] (K : Type v) [Field K] [Algebra R K]
    [Module.Finite R (integralClosure R K)] [Finite (MaximalSpectrum R)] :
    Finite (MaximalSpectrum (integralClosure R K)) :=
  finite_maximalSpectrum_of_moduleFinite R (integralClosure R K)

/-- A semilocal domain of dimension at most one has finite prime spectrum. -/
theorem finite_primeSpectrum_of_semilocal_dimensionLE_one
    (R : Type u) [CommRing R] [IsDomain R] [Finite (MaximalSpectrum R)]
    [Ring.KrullDimLE 1 R] : Finite (PrimeSpectrum R) := by
  classical
  let finiteIdeals : Set (Ideal R) := {⊥} ∪ Set.range MaximalSpectrum.asIdeal
  have hfinite : finiteIdeals.Finite := (Set.finite_singleton _).union (Set.finite_range _)
  let : Fintype finiteIdeals := hfinite.fintype
  let f : PrimeSpectrum R → finiteIdeals := fun P => ⟨P.asIdeal, by
    by_cases h : P.asIdeal = ⊥
    · exact Or.inl h
    · exact Or.inr ⟨⟨P.asIdeal, P.isPrime.isMaximal_of_ne_bot h⟩, rfl⟩⟩
  exact Finite.of_injective f (fun P Q h => PrimeSpectrum.ext (congrArg Subtype.val h))

/-- Every localization of a semilocal domain of dimension at most one is
semilocal. The dimension assumption is essential for this assertion. -/
theorem finite_maximalSpectrum_localization_of_dimensionLE_one
    (R : Type u) [CommRing R] [IsDomain R] [Finite (MaximalSpectrum R)]
    [Ring.KrullDimLE 1 R] (M : Submonoid R)
    (S : Type v) [CommRing S] [Algebra R S] [IsLocalization M S] :
    Finite (MaximalSpectrum S) := by
  let : Finite (PrimeSpectrum R) := finite_primeSpectrum_of_semilocal_dimensionLE_one R
  let : Finite (PrimeSpectrum S) :=
    Finite.of_injective (IsLocalization.primeSpectrumOrderIso M S)
      (IsLocalization.primeSpectrumOrderIso M S).injective
  exact Finite.of_injective MaximalSpectrum.toPrimeSpectrum
    MaximalSpectrum.toPrimeSpectrum_injective

/-- A conductor element remains a conductor after localizing both rings at the
same source denominators, using their literal images in the fraction field. -/
theorem conductor_mem_localized_subalgebra
    (R : Type u) [CommRing R] [IsDomain R] (K : Type v) [Field K]
    [Algebra R K] [IsFractionRing R K] (E : Subalgebra R K)
    (M : Submonoid R) (hM : M ≤ nonZeroDivisors R)
    (hME : M.map (algebraMap R E) ≤ nonZeroDivisors E)
    {c : R} (hc : ∀ x : E, ∃ r : R,
      algebraMap R K r = algebraMap R K c * (x : K))
    (x : Localization.subalgebra.ofField K (M.map (algebraMap R E)) hME) :
    algebraMap R K c * (x : K) ∈ Localization.subalgebra.ofField K M hM := by
  obtain ⟨a, s, hs, hx⟩ := x.property
  obtain ⟨s, hs, rfl⟩ := hs
  obtain ⟨r, hr⟩ := hc a
  refine ⟨r, s, hs, ?_⟩
  rw [hx, ← mul_assoc]
  change algebraMap R K c * (a : K) *
    (algebraMap E K (algebraMap R E s))⁻¹ = _
  rw [← hr, ← IsScalarTower.algebraMap_apply]

/-- Normalization in a fixed fraction field commutes with localization, as an
identity of the literal embedded subrings. -/
theorem normalization_localization_eq
    (R : Type u) [CommRing R] [IsDomain R] (K : Type v) [Field K]
    [Algebra R K] [IsFractionRing R K]
    (M : Submonoid R) (hM : M ≤ nonZeroDivisors R)
    (hMB : M.map (algebraMap R (integralClosure R K)) ≤
      nonZeroDivisors (integralClosure R K)) :
    (integralClosure (Localization.subalgebra.ofField K M hM) K).toSubring =
      (Localization.subalgebra.ofField K
        (M.map (algebraMap R (integralClosure R K))) hMB).toSubring := by
  let T := Localization.subalgebra.ofField K M hM
  ext x
  constructor
  · intro hx
    obtain ⟨s, hs⟩ := IsIntegral.exists_multiple_integral_of_isLocalization
      (Rₘ := T) M x hx
    let a : integralClosure R K := ⟨algebraMap R K s * x, by
      exact (mem_integralClosure_iff R K).mpr (by
        simpa only [Submonoid.smul_def, Algebra.smul_def] using hs)⟩
    refine ⟨a, algebraMap R (integralClosure R K) s,
      ⟨s, s.property, rfl⟩, ?_⟩
    change x = (algebraMap R K s * x) *
      (algebraMap (integralClosure R K) K (algebraMap R (integralClosure R K) s))⁻¹
    rw [← IsScalarTower.algebraMap_apply]
    have hs0 : algebraMap R K s ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr
        (nonZeroDivisors.ne_zero (hM s.property))
    field_simp
  · rintro ⟨a, s, hs, hx⟩
    obtain ⟨s, hs, rfl⟩ := hs
    have ha : IsIntegral T (a : K) := a.property.tower_top
    have hinvT : (algebraMap R K s)⁻¹ ∈ T := by
      refine ⟨1, s, hs, ?_⟩
      simp
    have hinv : IsIntegral T ((algebraMap R K s)⁻¹) := by
      exact (integralClosure T K).algebraMap_mem (⟨_, hinvT⟩ : T)
    rw [hx]
    apply (mem_integralClosure_iff T K).mpr
    simpa [← IsScalarTower.algebraMap_apply, Subalgebra.algebraMap_eq] using ha.mul hinv

/-- Nonzero source denominators remain nonzero in every intermediate algebra. -/
theorem subalgebra_map_le_nonZeroDivisors
    (R : Type u) [CommRing R] [IsDomain R] (K : Type v) [Field K]
    [Algebra R K] [IsFractionRing R K] (E : Subalgebra R K)
    (M : Submonoid R) (hM : M ≤ nonZeroDivisors R) :
    M.map (algebraMap R E) ≤ nonZeroDivisors E := by
  rintro _ ⟨r, hr, rfl⟩
  apply mem_nonZeroDivisors_iff_ne_zero.mpr
  intro h
  have hK : algebraMap R K r = 0 := congrArg Subtype.val h
  exact nonZeroDivisors.ne_zero (hM hr) ((IsFractionRing.injective R K)
    (hK.trans (map_zero _).symm))

/-- A one-dimensional semilocal normalization remains semilocal after localizing
the source. The target is the actual normalization of that localization. -/
theorem finite_maximalSpectrum_normalization_localization
    (R : Type u) [CommRing R] [IsDomain R] (K : Type v) [Field K]
    [Algebra R K] [IsFractionRing R K]
    [Finite (MaximalSpectrum (integralClosure R K))]
    [Ring.KrullDimLE 1 (integralClosure R K)]
    (M : Submonoid R) (hM : M ≤ nonZeroDivisors R) :
    Finite (MaximalSpectrum
      (integralClosure (Localization.subalgebra.ofField K M hM) K)) := by
  let hMB := subalgebra_map_le_nonZeroDivisors R K (integralClosure R K) M hM
  have hfin := finite_maximalSpectrum_localization_of_dimensionLE_one
    (integralClosure R K) (M.map (algebraMap R (integralClosure R K)))
    (Localization.subalgebra.ofField K (M.map (algebraMap R (integralClosure R K))) hMB)
  change Finite (MaximalSpectrum
    (integralClosure (Localization.subalgebra.ofField K M hM) K).toSubring)
  rw [normalization_localization_eq R K M hM hMB]
  exact hfin

/-- A global normalization conductor still multiplies the localized
normalization into the localized source. -/
theorem conductor_mem_normalization_localization
    (R : Type u) [CommRing R] [IsDomain R] (K : Type v) [Field K]
    [Algebra R K] [IsFractionRing R K]
    (M : Submonoid R) (hM : M ≤ nonZeroDivisors R)
    {c : R} (hc : ∀ x : integralClosure R K, ∃ r : R,
      algebraMap R K r = algebraMap R K c * (x : K))
    (x : integralClosure (Localization.subalgebra.ofField K M hM) K) :
    algebraMap R K c * (x : K) ∈ Localization.subalgebra.ofField K M hM := by
  let hMB := subalgebra_map_le_nonZeroDivisors R K (integralClosure R K) M hM
  have hx : (x : K) ∈ Localization.subalgebra.ofField K
      (M.map (algebraMap R (integralClosure R K))) hMB := by
    rw [← SetLike.mem_coe, ← Subalgebra.coe_toSubring,
      ← normalization_localization_eq R K M hM hMB]
    exact x.property
  exact conductor_mem_localized_subalgebra R K (integralClosure R K) M hM hMB hc ⟨x, hx⟩

end HereditaryAtomicity
