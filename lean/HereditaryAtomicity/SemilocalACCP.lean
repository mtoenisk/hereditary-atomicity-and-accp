import Factorization.PrincipalIdeals
import HereditaryAtomicity.SemilocalTransfer
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Spectrum.Maximal.Basic
import Mathlib.RingTheory.Localization.AsSubring

/-!
# ACCP from finitely many maximal localizations

ACCP at a maximal localization eventually makes each ratio of a nonzero divisibility
chain a unit there. Finiteness of the maximal spectrum supplies a common index after
which all ratios are units in the domain.
-/

namespace HereditaryAtomicity

universe u v

/-- A semilocal domain satisfies ACCP if every actual maximal localization does. -/
theorem wfDvdMonoid_of_maximal_localizations
    {R : Type u} [CommRing R] [IsDomain R] [Finite (MaximalSpectrum R)]
    (hlocal : ∀ M : MaximalSpectrum R,
      WfDvdMonoid (Localization.AtPrime M.asIdeal)) : WfDvdMonoid R := by
  classical
  let : Fintype (MaximalSpectrum R) := Fintype.ofFinite _
  by_contra hR
  obtain ⟨x, a, hx, ha, hxa⟩ :=
    Factorization.not_wfDvdMonoid_iff_exists_nonunit_chain.mp hR
  have hlocalUnit : ∀ M : MaximalSpectrum R, ∃ N : ℕ, ∀ n, N ≤ n →
      IsUnit (algebraMap R (Localization.AtPrime M.asIdeal) (a n)) := by
    intro M
    let f := algebraMap R (Localization.AtPrime M.asIdeal)
    apply Factorization.eventually_isUnit_ratios_of_wfDvdMonoid (hlocal M)
      (fun n => f (x n)) (fun n => f (a n))
    · intro n hzero
      exact hx n ((IsLocalization.injective (Localization.AtPrime M.asIdeal)
        M.asIdeal.primeCompl_le_nonZeroDivisors) (hzero.trans (map_zero _).symm))
    · intro n
      simpa only [map_mul] using congrArg f (hxa n)
  choose N hN using hlocalUnit
  let n := Finset.univ.sup N
  obtain ⟨M, hM, haM⟩ := exists_max_ideal_of_mem_nonunits (ha n)
  let P : MaximalSpectrum R := ⟨M, hM⟩
  have hunit := hN P n (Finset.le_sup (Finset.mem_univ P))
  exact (IsLocalization.AtPrime.isUnit_to_map_iff (Localization.AtPrime M) M (a n)).mp
    hunit haM

/-- For a semilocal HA domain, ACCP at its maximal stalks implies hereditary
ACCP of the source. HA is assumed only for the source, not for its stalks. -/
theorem hereditarilyACCP_of_maximal_localizations
    {R : Type u} [CommRing R] [IsDomain R] [Finite (MaximalSpectrum R)]
    (hR : Factorization.IsHereditarilyAtomic R)
    (hlocal : ∀ M : MaximalSpectrum R,
      WfDvdMonoid (Localization.AtPrime M.asIdeal)) :
    Factorization.IsHereditarilyACCP R :=
  semilocal_hereditarilyACCP hR (wfDvdMonoid_of_maximal_localizations hlocal)

/-- The local-to-global ACCP criterion also accepts the literal maximal
localization subrings of any specified actual fraction field. -/
theorem wfDvdMonoid_of_embedded_maximal_localizations
    (R : Type u) [CommRing R] [IsDomain R] [Finite (MaximalSpectrum R)]
    (K : Type v) [Field K] [Algebra R K] [IsFractionRing R K]
    (hlocal : ∀ M : MaximalSpectrum R, WfDvdMonoid
      (Localization.subalgebra.ofField K M.asIdeal.primeCompl
        M.asIdeal.primeCompl_le_nonZeroDivisors)) : WfDvdMonoid R := by
  apply wfDvdMonoid_of_maximal_localizations
  intro M
  exact (Factorization.wfDvdMonoid_ringEquiv_iff
    (IsLocalization.algEquiv M.asIdeal.primeCompl (Localization.AtPrime M.asIdeal)
      (Localization.subalgebra.ofField K M.asIdeal.primeCompl
        M.asIdeal.primeCompl_le_nonZeroDivisors)).toRingEquiv).mp (hlocal M)

end HereditaryAtomicity
