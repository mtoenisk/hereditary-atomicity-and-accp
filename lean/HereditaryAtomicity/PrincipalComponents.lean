import Mathlib.RingTheory.DedekindDomain.PID
import Mathlib.RingTheory.LocalProperties.Basic
import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.Ideal.IsPrimary

/-!
# Principal components in semilocal domains of dimension at most one

The active component at a maximal ideal is the contraction of a principal ideal
from the actual localization. Finite maximal spectrum makes these components
principal; no Noetherianity, normality or hereditary factorization is assumed.
-/

open scoped nonZeroDivisors

noncomputable section
namespace HereditaryAtomicity

universe u
variable {R : Type u} [CommRing R]

/-- The actual contraction of the principal ideal from a prime localization. -/
def principalComponent (P : Ideal R) [P.IsPrime] (a : R) : Ideal R :=
  (Ideal.span {algebraMap R (Localization.AtPrime P) a}).under R

/-- Extending an active contraction recovers the original principal ideal. -/
theorem principalComponent_map_self (P : Ideal R) [P.IsPrime] (a : R) :
    (principalComponent P a).map (algebraMap R (Localization.AtPrime P)) =
      Ideal.span {algebraMap R (Localization.AtPrime P) a} :=
  IsLocalization.map_under P.primeCompl _ _

theorem principalComponent_eq_top_of_not_mem (P : Ideal R) [P.IsPrime] {a : R}
    (ha : a ∉ P) : principalComponent P a = ⊤ := by
  have hunit := (IsLocalization.AtPrime.isUnit_to_map_iff (Localization.AtPrime P) P a).mpr ha
  simp [principalComponent, Ideal.span_singleton_eq_top.mpr hunit]

theorem localizationAtPrime_krullDimLE_one [Ring.KrullDimLE 1 R]
    (P : Ideal R) [P.IsPrime] : Ring.KrullDimLE 1 (Localization.AtPrime P) := by
  apply Ring.krullDimLE_iff.mpr
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height P]
  exact Ideal.height_le_ringKrullDim_of_isPrime.trans
    (Ring.krullDimLE_iff.mp inferInstance)

/-- In a one-dimensional local domain, the radical of every proper nonzero
principal ideal is the maximal ideal. -/
theorem radical_span_eq_maximalIdeal [IsDomain R] [IsLocalRing R] [Ring.KrullDimLE 1 R]
    {a : R} (ha : a ≠ 0) (hau : ¬ IsUnit a) :
    (Ideal.span {a}).radical = IsLocalRing.maximalIdeal R := by
  apply le_antisymm
  · apply (Ideal.IsPrime.radical_le_iff (inferInstance : (IsLocalRing.maximalIdeal R).IsPrime)).mpr
    exact Ideal.span_le.mpr (Set.singleton_subset_iff.mpr ((IsLocalRing.mem_maximalIdeal a).mpr hau))
  · rw [Ideal.radical_eq_sInf]
    apply le_sInf
    rintro P ⟨haP, hP⟩
    have hP0 : P ≠ ⊥ := by
      intro he
      have := haP (Ideal.subset_span (Set.mem_singleton a))
      exact ha (by simpa [he] using this)
    have hPm := IsLocalRing.eq_maximalIdeal (hP.isMaximal_of_ne_bot hP0)
    exact hPm ▸ le_rfl

theorem principalComponent_radical [IsDomain R] [Ring.KrullDimLE 1 R]
    (P : Ideal R) [P.IsMaximal] {a : R} (ha : a ≠ 0) (haP : a ∈ P) :
    (principalComponent P a).radical = P := by
  let : Ring.KrullDimLE 1 (Localization.AtPrime P) := localizationAtPrime_krullDimLE_one P
  have ha0 : algebraMap R (Localization.AtPrime P) a ≠ 0 :=
    by simpa using (IsLocalization.injective (Localization.AtPrime P) P.primeCompl_le_nonZeroDivisors).ne ha
  have hau : ¬ IsUnit (algebraMap R (Localization.AtPrime P) a) := by
    intro hu
    exact ((IsLocalization.AtPrime.isUnit_to_map_iff (Localization.AtPrime P) P a).mp hu) haP
  rw [principalComponent, Ideal.under_def, ← Ideal.comap_radical,
    radical_span_eq_maximalIdeal ha0 hau]
  exact IsLocalization.AtPrime.under_maximalIdeal _ P

theorem principalComponent_map_other [IsDomain R] [Ring.KrullDimLE 1 R]
    (P Q : Ideal R) [P.IsMaximal] [Q.IsMaximal] (hne : P ≠ Q)
    {a : R} (ha : a ≠ 0) :
    (principalComponent P a).map (algebraMap R (Localization.AtPrime Q)) = ⊤ := by
  by_cases haP : a ∈ P
  · apply IsLocalization.AtPrime.map_eq_top_of_not_le (Localization.AtPrime Q) (p := Q)
    intro hle
    have hPQ : P ≤ Q := by
      rw [← principalComponent_radical P ha haP]
      exact (Ideal.radical_mono hle).trans_eq (Ideal.IsPrime.radical (inferInstance : Q.IsPrime))
    exact hne (Ideal.IsMaximal.eq_of_le ‹P.IsMaximal› ‹Q.IsMaximal›.ne_top hPQ)
  · rw [principalComponent_eq_top_of_not_mem P haP, Ideal.map_top]


/-- Nonzero principal ideals are the finite product of their active contractions. -/
theorem prod_principalComponent [IsDomain R] [Ring.KrullDimLE 1 R]
    [Fintype (MaximalSpectrum R)] {a : R} (ha : a ≠ 0) :
    (∏ P : MaximalSpectrum R, principalComponent P.asIdeal a) = Ideal.span {a} := by
  classical
  apply Ideal.eq_of_localization_maximal
  intro Q hQ
  let Q' : MaximalSpectrum R := ⟨Q, hQ⟩
  change (Ideal.mapHom (algebraMap R (Localization.AtPrime Q))) _ = _
  rw [map_prod]
  rw [Finset.prod_eq_single Q']
  · exact (principalComponent_map_self Q a).trans (by simp [Ideal.map_span])
  · intro P _ hPQ
    change (principalComponent P.asIdeal a).map _ = 1
    rw [principalComponent_map_other P.asIdeal Q (by
      intro h
      apply hPQ
      exact MaximalSpectrum.ext h) ha]
    exact Ideal.one_eq_top.symm
  · simp

/-- Semilocality makes every nonzero active contraction principal. -/
theorem principalComponent_isPrincipal [IsDomain R] [Ring.KrullDimLE 1 R]
    [Finite (MaximalSpectrum R)] (P : Ideal R) [P.IsMaximal] {a : R} (ha : a ≠ 0) :
    (principalComponent P a).IsPrincipal := by
  classical
  let : Fintype (MaximalSpectrum R) := Fintype.ofFinite _
  let f : Ideal R →+* FractionalIdeal R⁰ (FractionRing R) :=
    FractionalIdeal.coeIdealHom R⁰ (FractionRing R)
  have hf : {I : Ideal R | I.IsMaximal}.Finite := by
    rw [← MaximalSpectrum.range_asIdeal]
    exact Set.finite_range MaximalSpectrum.asIdeal
  apply Ideal.IsPrincipal.of_finite_maximals_of_isUnit hf
  have hu : IsUnit (f (Ideal.span {a})) :=
    IsUnit.of_mul_eq_one _ (FractionalIdeal.coe_ideal_span_singleton_mul_inv (FractionRing R) ha)
  have hprod := congrArg f (prod_principalComponent ha)
  rw [map_prod] at hprod
  rw [← hprod] at hu
  exact (IsUnit.prod_univ_iff.mp hu) ⟨P, inferInstance⟩


/-- Active contractions multiply exactly, without a factoriality hypothesis. -/
theorem principalComponent_mul [IsDomain R] [Ring.KrullDimLE 1 R]
    (P : Ideal R) [P.IsMaximal] {a b : R} (ha : a ≠ 0) (hb : b ≠ 0) :
    principalComponent P (a * b) = principalComponent P a * principalComponent P b := by
  apply Ideal.eq_of_localization_maximal
  intro Q hQ
  by_cases hPQ : P = Q
  · subst Q
    rw [Ideal.map_mul, principalComponent_map_self, principalComponent_map_self,
      principalComponent_map_self, map_mul, Ideal.span_singleton_mul_span_singleton]
  · rw [Ideal.map_mul, principalComponent_map_other P Q hPQ (mul_ne_zero ha hb),
      principalComponent_map_other P Q hPQ ha, principalComponent_map_other P Q hPQ hb,
      Ideal.top_mul]


theorem mem_principalComponent_self (P : Ideal R) [P.IsPrime] (a : R) :
    a ∈ principalComponent P a :=
  Ideal.subset_span (Set.mem_singleton _)

/-- A source atom contained in a maximal ideal is its own active component. -/
theorem principalComponent_irreducible [IsDomain R] [Ring.KrullDimLE 1 R]
    [Finite (MaximalSpectrum R)] (P : Ideal R) [P.IsMaximal] {a : R}
    (ha : Irreducible a) (haP : a ∈ P) :
    principalComponent P a = Ideal.span {a} := by
  let : (principalComponent P a).IsPrincipal := principalComponent_isPrincipal P ha.ne_zero
  let b := Submodule.IsPrincipal.generator (principalComponent P a)
  have hb : Ideal.span {b} = principalComponent P a := Ideal.span_singleton_generator _
  have hbQ : b ∈ principalComponent P a := hb ▸ Ideal.subset_span (Set.mem_singleton b)
  have hbP : b ∈ P := by
    rw [← principalComponent_radical P ha.ne_zero haP]
    exact Ideal.le_radical hbQ
  have hbu : ¬ IsUnit b := fun h => ‹P.IsMaximal›.ne_top (P.eq_top_of_isUnit_mem hbP h)
  have hbdiv : b ∣ a := Ideal.mem_span_singleton.mp (hb.symm ▸ mem_principalComponent_self P a)
  have hab : Associated a b := (ha.dvd_iff.mp hbdiv).resolve_left hbu
  exact hb.symm.trans (Ideal.span_singleton_eq_span_singleton.mpr hab.symm)

/-- Every atom in a semilocal domain of dimension at most one has a unique
maximal support. -/
theorem irreducible_unique_maximal [IsDomain R] [Ring.KrullDimLE 1 R]
    [Finite (MaximalSpectrum R)] {a : R} (ha : Irreducible a)
    (P Q : Ideal R) [P.IsMaximal] [Q.IsMaximal] (haP : a ∈ P) (haQ : a ∈ Q) : P = Q := by
  rw [← principalComponent_radical P ha.ne_zero haP,
    ← principalComponent_radical Q ha.ne_zero haQ,
    principalComponent_irreducible P ha haP, principalComponent_irreducible Q ha haQ]

end HereditaryAtomicity
