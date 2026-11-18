import HereditaryAtomicity.Pruefer
import Mathlib.RingTheory.KrullDimension.Zero
import Mathlib.RingTheory.LocalProperties.Submodule
import Mathlib.Topology.Separation.Profinite
import Mathlib.Topology.Connected.Separation

/-! # Principalization in one-dimensional Prüfer domains with nonzero Jacobson radical

The proof glues local generators using clopens in the zero-dimensional quotient
by the Jacobson radical. No finiteness of the maximal spectrum is required.
-/

noncomputable section
namespace HereditaryAtomicity

open Set TopologicalSpace

/-- A basic open in a zero-dimensional affine spectrum is also closed. -/
theorem isClopen_basicOpen_of_dimension_zero
    {A : Type*} [CommRing A] [Ring.KrullDimLE 0 A] (a : A) :
    IsClopen (PrimeSpectrum.basicOpen a : Set (PrimeSpectrum A)) := by
  refine ⟨?_, (PrimeSpectrum.basicOpen a).isOpen⟩
  rw [← isOpen_compl_iff]
  apply isOpen_iff_forall_mem_open.mpr
  intro P hP
  have ha : a ∈ P.asIdeal := by simpa using hP
  let L := Localization.AtPrime P.asIdeal
  let : Ring.KrullDimLE 0 L := Ring.KrullDimLE.of_isLocalization P.asIdeal
    ((Ring.KrullDimLE.mem_minimalPrimes_iff).mpr ⟨P.isPrime, bot_le⟩) L
  have han : IsNilpotent (algebraMap A L a) :=
    Ring.KrullDimLE.isNilpotent_iff_mem_maximalIdeal.mpr
      ((IsLocalization.AtPrime.to_map_mem_maximal_iff L P.asIdeal a).mpr ha)
  obtain ⟨n, hn⟩ := han
  obtain ⟨s, hs⟩ := (IsLocalization.map_eq_zero_iff P.asIdeal.primeCompl L (a ^ n)).mp
    (by simpa using hn)
  refine ⟨PrimeSpectrum.basicOpen (s : A), ?_, (PrimeSpectrum.basicOpen _).isOpen,
    s.property⟩
  intro Q hQ
  change ¬ a ∉ Q.asIdeal
  intro hQa
  have hmul : (s : A) * a ^ n ∈ Q.asIdeal := hs ▸ Q.asIdeal.zero_mem
  have hpow : a ^ n ∈ Q.asIdeal := (Q.isPrime.mem_or_mem hmul).resolve_left hQ
  exact hQa (Q.isPrime.mem_of_pow_mem n hpow)

/-- Zero-dimensional affine spectra are totally separated. -/
theorem totallySeparated_primeSpectrum_of_dimension_zero
    {A : Type*} [CommRing A] [Ring.KrullDimLE 0 A] :
    TotallySeparatedSpace (PrimeSpectrum A) := by
  apply totallySeparatedSpace_iff_exists_isClopen.mpr
  intro P Q hPQ
  have hnle : ¬ Q.asIdeal ≤ P.asIdeal := by
    intro h
    exact hPQ (PrimeSpectrum.ext
      ((Q.isPrime.isMaximal').eq_of_le P.isPrime.ne_top h).symm)
  obtain ⟨a, haQ, haP⟩ := SetLike.not_le_iff_exists.mp hnle
  exact ⟨PrimeSpectrum.basicOpen a, isClopen_basicOpen_of_dimension_zero a, haP, by simpa using haQ⟩

/-- Local divisibility is witnessed on a principal neighborhood. -/
theorem exists_mul_dvd_of_localization_dvd
    {A : Type*} [CommRing A] [IsDomain A] (P : Ideal A) [P.IsPrime]
    {a b : A}
    (h : algebraMap A (Localization.AtPrime P) a ∣
      algebraMap A (Localization.AtPrime P) b) :
    ∃ s : A, s ∉ P ∧ a ∣ s * b := by
  let L := Localization.AtPrime P
  obtain ⟨q, hq⟩ := h
  obtain ⟨⟨t, s⟩, hs⟩ := IsLocalization.surj P.primeCompl q
  refine ⟨s, s.property, t, ?_⟩
  apply IsLocalization.injective L P.primeCompl_le_nonZeroDivisors
  simp only [map_mul]
  calc
    algebraMap A L (s : A) * algebraMap A L b =
        algebraMap A L (s : A) * (algebraMap A L a * q) := by rw [hq]
    _ = algebraMap A L a * (q * algebraMap A L (s : A)) := by ring
    _ = algebraMap A L a * algebraMap A L t := by rw [hs]

/-- A nonzero quotient of a one-dimensional domain is zero-dimensional. -/
theorem dimension_zero_quotient_of_nonzero_ideal
    {A : Type*} [CommRing A] [IsDomain A] [Ring.KrullDimLE 1 A]
    (J : Ideal A) (hJ : J ≠ ⊥) : Ring.KrullDimLE 0 (A ⧸ J) := by
  apply Ring.KrullDimLE.mk₀
  intro Q hQ
  let q := Ideal.Quotient.mk J
  let P := Q.comap q
  have hP : P.IsPrime := Ideal.comap_isPrime q Q
  have hJP : J ≤ P := by
    simpa [q] using (Ideal.ker_le_comap (K := Q) q)
  have hPn : P ≠ ⊥ := fun h => hJ (le_antisymm (h ▸ hJP) bot_le)
  have hPm : P.IsMaximal := hP.isMaximal_of_ne_bot hPn
  have hmap := Ideal.map_eq_top_or_isMaximal_of_surjective q Ideal.Quotient.mk_surjective hPm
  rw [Ideal.map_comap_of_surjective q Ideal.Quotient.mk_surjective] at hmap
  exact hmap.resolve_left hQ.ne_top

/-- The principal neighborhoods where the first element divides the second. -/
def divisibilityLocus
    {A : Type*} [CommRing A] (J : Ideal A) (a b : A) : Set (PrimeSpectrum (A ⧸ J)) :=
  ⋃ s : {s : A // a ∣ s * b}, (PrimeSpectrum.basicOpen (Ideal.Quotient.mk J s) : Set _)

theorem isOpen_divisibilityLocus
    {A : Type*} [CommRing A] (J : Ideal A) (a b : A) :
    IsOpen (divisibilityLocus J a b) :=
  isOpen_iUnion fun _ => (PrimeSpectrum.basicOpen _).isOpen

theorem mem_divisibilityLocus_iff
    {A : Type*} [CommRing A] (J : Ideal A) (a b : A)
    (Q : PrimeSpectrum (A ⧸ J)) :
    Q ∈ divisibilityLocus J a b ↔
      ∃ s : A, a ∣ s * b ∧ s ∉ Q.asIdeal.comap (Ideal.Quotient.mk J) := by
  simp only [divisibilityLocus, Set.mem_iUnion]
  constructor
  · rintro ⟨s, hs⟩
    exact ⟨s, s.property, hs⟩
  · rintro ⟨s, hds, hs⟩
    exact ⟨⟨s, hds⟩, hs⟩

/-- In a Prüfer domain the two divisibility loci cover the quotient spectrum. -/
theorem divisibilityLocus_union_eq_univ
    {A : Type*} [CommRing A] [IsDomain A]
    (hA : IsPrueferDomain A) (J : Ideal A) (a b : A) :
    divisibilityLocus J a b ∪ divisibilityLocus J b a = Set.univ := by
  apply Set.eq_univ_of_forall
  intro Q
  let P := Q.asIdeal.comap (Ideal.Quotient.mk J)
  let : P.IsPrime := Ideal.comap_isPrime _ _
  let : ValuationRing (Localization.AtPrime P) := hA P
  rcases ValuationRing.dvd_total
      (algebraMap A (Localization.AtPrime P) a)
      (algebraMap A (Localization.AtPrime P) b) with hab | hba
  · obtain ⟨s, hs, hds⟩ := exists_mul_dvd_of_localization_dvd P hab
    exact Or.inl ((mem_divisibilityLocus_iff J a b Q).mpr ⟨s, hds, hs⟩)
  · obtain ⟨s, hs, hds⟩ := exists_mul_dvd_of_localization_dvd P hba
    exact Or.inr ((mem_divisibilityLocus_iff J b a Q).mpr ⟨s, hds, hs⟩)

/-- Divisibility in a domain can be checked at every maximal localization. -/
theorem dvd_of_dvd_at_all_maximal_localizations
    {A : Type*} [CommRing A] [IsDomain A] {a b : A}
    (h : ∀ (P : Ideal A) [P.IsMaximal],
      algebraMap A (Localization.AtPrime P) a ∣ algebraMap A (Localization.AtPrime P) b) :
    a ∣ b := by
  let I : Ideal A :=
    { carrier := {s | a ∣ s * b}
      zero_mem' := by simp
      add_mem' := by
        intro x y hx hy
        change a ∣ (x + y) * b
        simpa only [add_mul] using dvd_add hx hy
      smul_mem' := by
        intro x y hy
        change a ∣ (x * y) * b
        simpa only [mul_assoc] using dvd_mul_of_dvd_right hy x }
  have hIt : I = ⊤ := by
    by_contra hI
    obtain ⟨P, hP, hIP⟩ := I.exists_le_maximal hI
    let : P.IsMaximal := hP
    obtain ⟨s, hs, hds⟩ := exists_mul_dvd_of_localization_dvd P (h P)
    exact hs (hIP hds)
  have h1 : (1 : A) ∈ I := by rw [hIt]; trivial
  simpa [I] using h1

/-- A unit coefficient and a maximal-ideal coefficient select the first local generator. -/
theorem local_generator_of_unit_coefficient
    {A : Type*} [CommRing A] [IsLocalRing A]
    {a b e f : A} (hab : a ∣ b) (he : IsUnit e)
    (hf : f ∈ IsLocalRing.maximalIdeal A) :
    e * a + f * b ∣ a ∧ e * a + f * b ∣ b := by
  obtain ⟨q, rfl⟩ := hab
  have hu : IsUnit (e + f * q) := by
    apply IsLocalRing.notMem_maximalIdeal.mp
    intro h
    have he' : e ∈ IsLocalRing.maximalIdeal A := by
      have := (IsLocalRing.maximalIdeal A).sub_mem h
        ((IsLocalRing.maximalIdeal A).mul_mem_right q hf)
      simpa using this
    exact (IsLocalRing.notMem_maximalIdeal.mpr he) he'
  have hd : e * a + f * (a * q) = a * (e + f * q) := by ring
  rw [hd]
  exact ⟨hu.mul_right_dvd.mpr dvd_rfl, hu.mul_right_dvd.mpr (dvd_mul_right a q)⟩

private theorem local_divisibility_of_mem_locus
    {A : Type*} [CommRing A] [IsDomain A] (J : Ideal A) (a b : A)
    (P : Ideal A) [P.IsPrime] (Q : PrimeSpectrum (A ⧸ J))
    (hQP : Q.asIdeal.comap (Ideal.Quotient.mk J) = P)
    (hQ : Q ∈ divisibilityLocus J a b) :
    algebraMap A (Localization.AtPrime P) a ∣ algebraMap A (Localization.AtPrime P) b := by
  let L := Localization.AtPrime P
  obtain ⟨s, hds, hs⟩ := (mem_divisibilityLocus_iff J a b Q).mp hQ
  have hsP : s ∉ P := by rwa [← hQP]
  have hu : IsUnit (algebraMap A L s) :=
    (IsLocalization.AtPrime.isUnit_to_map_iff L P s).mpr hsP
  apply hu.dvd_mul_left.mp
  simpa using map_dvd (algebraMap A L) hds

/-- A Prüfer domain whose Jacobson quotient is zero-dimensional is Bézout.
The quotient need not be finite and the maximal spectrum need not be finite. -/
theorem isBezout_of_pruefer_of_dimension_zero_jacobson_quotient
    {A : Type*} [CommRing A] [IsDomain A]
    (hA : IsPrueferDomain A)
    [Ring.KrullDimLE 0 (A ⧸ Ideal.jacobson (⊥ : Ideal A))] : IsBezout A := by
  classical
  apply IsBezout.iff_span_pair_isPrincipal.mpr
  intro a b
  let J := Ideal.jacobson (⊥ : Ideal A)
  let q := Ideal.Quotient.mk J
  let U := divisibilityLocus J a b
  let V := divisibilityLocus J b a
  let : TotallySeparatedSpace (PrimeSpectrum (A ⧸ J)) :=
    totallySeparated_primeSpectrum_of_dimension_zero
  have hcover : U ∪ V = Set.univ := divisibilityLocus_union_eq_univ hA J a b
  have hVU : Vᶜ ⊆ U := by
    intro Q hQ
    have : Q ∈ U ∪ V := hcover ▸ Set.mem_univ Q
    exact this.resolve_right hQ
  obtain ⟨W, hW, hVW, hWU⟩ := exists_clopen_of_closed_subset_open
    (isOpen_divisibilityLocus J b a).isClosed_compl
    (isOpen_divisibilityLocus J a b) hVU
  obtain ⟨e₀, f₀, _, _, hWe, hWf⟩ :=
    PrimeSpectrum.exists_mul_eq_zero_add_eq_one_basicOpen_eq_of_isClopen hW
  obtain ⟨e, he⟩ := Ideal.Quotient.mk_surjective e₀
  obtain ⟨f, hf⟩ := Ideal.Quotient.mk_surjective f₀
  let d := e * a + f * b
  have hdlocal : ∀ (P : Ideal A) [P.IsPrime] (Q : PrimeSpectrum (A ⧸ J)),
      Q.asIdeal.comap q = P →
      algebraMap A (Localization.AtPrime P) d ∣ algebraMap A (Localization.AtPrime P) a ∧
      algebraMap A (Localization.AtPrime P) d ∣ algebraMap A (Localization.AtPrime P) b := by
    intro P _ Q hQP
    let L := Localization.AtPrime P
    by_cases hQ : Q ∈ W
    · have heQ : e ∉ P := by
        rw [← hQP]
        change q e ∉ Q.asIdeal
        rw [he]
        change Q ∈ (PrimeSpectrum.basicOpen e₀ : Set _)
        rw [← hWe]
        exact hQ
      have hfQ : f ∈ P := by
        rw [← hQP]
        change q f ∈ Q.asIdeal
        rw [hf]
        by_contra hfn
        have : Q ∈ Wᶜ := hWf.symm ▸ hfn
        exact this hQ
      have hab := local_divisibility_of_mem_locus J a b P Q hQP (hWU hQ)
      have hgen := local_generator_of_unit_coefficient hab
        ((IsLocalization.AtPrime.isUnit_to_map_iff L P e).mpr heQ)
        ((IsLocalization.AtPrime.to_map_mem_maximal_iff L P f).mpr hfQ)
      simpa only [d, map_add, map_mul] using hgen
    · have hfQ : f ∉ P := by
        rw [← hQP]
        change q f ∉ Q.asIdeal
        rw [hf]
        change Q ∈ (PrimeSpectrum.basicOpen f₀ : Set _)
        rw [← hWf]
        exact hQ
      have heQ : e ∈ P := by
        rw [← hQP]
        change q e ∈ Q.asIdeal
        rw [he]
        by_contra hen
        have : Q ∈ W := hWe.symm ▸ hen
        exact hQ this
      have hQV : Q ∈ V := by
        by_contra hQV
        exact hQ (hVW hQV)
      have hba := local_divisibility_of_mem_locus J b a P Q hQP hQV
      have hgen := local_generator_of_unit_coefficient hba
        ((IsLocalization.AtPrime.isUnit_to_map_iff L P f).mpr hfQ)
        ((IsLocalization.AtPrime.to_map_mem_maximal_iff L P e).mpr heQ)
      have hd : algebraMap A L d =
          algebraMap A L f * algebraMap A L b + algebraMap A L e * algebraMap A L a := by
        change algebraMap A L (e * a + f * b) = _
        rw [map_add, map_mul, map_mul]
        exact add_comm _ _
      rw [hd]
      exact hgen.symm
  have hdmax : ∀ (P : Ideal A) [P.IsMaximal],
      algebraMap A (Localization.AtPrime P) d ∣ algebraMap A (Localization.AtPrime P) a ∧
      algebraMap A (Localization.AtPrime P) d ∣ algebraMap A (Localization.AtPrime P) b := by
    intro P hP
    have hJP : J ≤ P := sInf_le ⟨bot_le, hP⟩
    let Q : PrimeSpectrum (A ⧸ J) :=
      ⟨P.map q, Ideal.isPrime_map_quotientMk_of_isPrime hJP⟩
    have hQP : Q.asIdeal.comap q = P := Ideal.comap_map_mk hJP
    exact hdlocal P Q hQP
  have hda : d ∣ a := dvd_of_dvd_at_all_maximal_localizations (fun P _ => (hdmax P).1)
  have hdb : d ∣ b := dvd_of_dvd_at_all_maximal_localizations (fun P _ => (hdmax P).2)
  refine ⟨⟨d, le_antisymm ?_ ?_⟩⟩
  · apply Ideal.span_le.mpr
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact Ideal.mem_span_singleton.mpr hda
    · exact Ideal.mem_span_singleton.mpr hdb
  · apply Ideal.span_le.mpr
    intro x hx
    obtain rfl := Set.mem_singleton_iff.mp hx
    exact Ideal.add_mem _
      (Ideal.mul_mem_left _ e (Ideal.subset_span (by simp)))
      (Ideal.mul_mem_left _ f (Ideal.subset_span (by simp)))

/-- One-dimensional Prüfer domains with nonzero Jacobson radical are Bézout. -/
theorem isBezout_of_pruefer_of_nonzero_jacobson
    {A : Type*} [CommRing A] [IsDomain A] [Ring.KrullDimLE 1 A]
    (hA : IsPrueferDomain A) (hJ : Ideal.jacobson (⊥ : Ideal A) ≠ ⊥) :
    IsBezout A := by
  let : Ring.KrullDimLE 0 (A ⧸ Ideal.jacobson (⊥ : Ideal A)) :=
    dimension_zero_quotient_of_nonzero_ideal _ hJ
  exact isBezout_of_pruefer_of_dimension_zero_jacobson_quotient hA

end HereditaryAtomicity
