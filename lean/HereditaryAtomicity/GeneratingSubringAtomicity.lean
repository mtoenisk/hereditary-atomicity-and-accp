import HereditaryAtomicity.ArithmeticUnitReflection
import HereditaryAtomicity.SemilocalDimension
import HereditaryAtomicity.SemilocalLocalization
import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Return to a source subring before localizing

The inverse image of a unit-reflecting subring reflects units in the source. Clearing
powers of a denominator that becomes invertible in the target subring gives a
localization presentation.
-/

noncomputable section

namespace HereditaryAtomicity

universe u v

/-- The actual map from the inverse-image subring into the target subring. -/
def subringPreimageMap {R : Type u} {T : Type v} [CommRing R] [CommRing T]
    (f : R →+* T) (C : Subring T) : C.comap f →+* C where
  toFun a := ⟨f a, a.property⟩
  map_zero' := Subtype.ext f.map_zero
  map_one' := Subtype.ext f.map_one
  map_add' a b := Subtype.ext (f.map_add a b)
  map_mul' a b := Subtype.ext (f.map_mul a b)

/-- Unit reflection survives inverse image along any ring homomorphism. -/
theorem subring_preimage_reflects_units
    {R : Type u} {T : Type v} [CommRing R] [CommRing T]
    (f : R →+* T) (C : Subring T)
    (hunit : ∀ c : C, IsUnit (c : T) → IsUnit c)
    (a : C.comap f) (ha : IsUnit (a : R)) : IsUnit a := by
  obtain ⟨u, hu⟩ := ha
  have hc : IsUnit (⟨f a, a.property⟩ : C) :=
    hunit _ ((hu ▸ u.isUnit).map f)
  obtain ⟨b, hb⟩ := hc.exists_right_inv
  have heq : f ((u⁻¹ : Rˣ) : R) = (b : T) := by
    have h := Units.inv_eq_of_mul_eq_one_right
      (u := Units.map f.toMonoidHom u) (a := (b : T))
      (by
        change f (u : R) * (b : T) = 1
        rw [hu]
        exact congrArg Subtype.val hb)
    change f ((u⁻¹ : Rˣ) : R) = (b : T) at h
    exact h
  have hinv : ((u⁻¹ : Rˣ) : R) ∈ C.comap f := by
    change f ((u⁻¹ : Rˣ) : R) ∈ C
    rw [heq]
    exact b.property
  apply IsUnit.of_mul_eq_one (⟨(u⁻¹ : Rˣ), hinv⟩ : C.comap f)
  apply Subtype.ext
  change (a : R) * ↑u⁻¹ = 1
  rw [← hu]
  exact u.val_inv

/-- A unit-reflecting subring of a localization pulls back to a semilocal
subring of a semilocal source. -/
theorem finite_maximalSpectrum_preimage_of_unit_reflection
    {R : Type u} {T : Type v} [CommRing R] [Nontrivial R] [CommRing T]
    [Finite (MaximalSpectrum R)] (f : R →+* T) (C : Subring T)
    (hunit : ∀ c : C, IsUnit (c : T) → IsUnit c) :
    Finite (MaximalSpectrum (C.comap f)) :=
  finite_maximalSpectrum_subring_of_unit_reflection (C.comap f)
    (subring_preimage_reflects_units f C hunit)

/-- Clearing a returned denominator identifies the target subring with the
localization of its actual inverse image in the source. -/
theorem subring_preimage_isLocalization_away
    {R : Type u} {T : Type v} [CommRing R] [CommRing T] [Algebra R T]
    (C : Subring T) (s : R) [IsLocalization.Away s T]
    (hs : algebraMap R T s ∈ C)
    (hsunit : IsUnit (⟨algebraMap R T s, hs⟩ : C)) :
    letI := (subringPreimageMap (algebraMap R T) C).toAlgebra
    IsLocalization.Away (⟨s, hs⟩ : C.comap (algebraMap R T)) C := by
  let := (subringPreimageMap (algebraMap R T) C).toAlgebra
  apply IsLocalization.Away.mk
  · exact hsunit
  · intro c
    obtain ⟨n, a, ha⟩ := IsLocalization.Away.surj s (c : T)
    have hac : algebraMap R T a ∈ C := ha ▸ C.mul_mem c.property (C.pow_mem hs n)
    refine ⟨n, ⟨a, hac⟩, Subtype.ext ?_⟩
    exact ha
  · intro a b hab
    have habT : algebraMap R T (a : R) = algebraMap R T (b : R) :=
      congrArg Subtype.val hab
    obtain ⟨n, hn⟩ := IsLocalization.Away.exists_of_eq s habT
    exact ⟨n, Subtype.ext hn⟩

/-- In dimension at most one, a finite maximal spectrum lets one denominator
represent the maximal support of an arbitrary multiplicative set. -/
theorem exists_single_localization_denominator
    {R : Type u} [CommRing R] [IsDomain R] [Finite (MaximalSpectrum R)]
    [Ring.KrullDimLE 1 R] (M : Submonoid R) (hM : (0 : R) ∉ M) :
    ∃ s ∈ M, ∀ m ∈ M, ∃ n : ℕ, m ∣ s ^ n := by
  classical
  let := Fintype.ofFinite (MaximalSpectrum R)
  have hchoose : ∀ P : MaximalSpectrum R,
      ∃ r ∈ M, (∃ m ∈ M, m ∈ P.asIdeal) → r ∈ P.asIdeal := by
    intro P
    by_cases h : ∃ m ∈ M, m ∈ P.asIdeal
    · obtain ⟨m, hm, hmP⟩ := h
      exact ⟨m, hm, fun _ => hmP⟩
    · exact ⟨1, M.one_mem, fun he => (h he).elim⟩
  choose r hr hrP using hchoose
  let s : R := ∏ P : MaximalSpectrum R, r P
  refine ⟨s, M.prod_mem (fun P _ => hr P), ?_⟩
  intro m hm
  have hm0 : m ≠ 0 := fun h => hM (h ▸ hm)
  have hsrad : s ∈ (Ideal.span ({m} : Set R)).radical := by
    rw [Ideal.radical_eq_sInf]
    apply Ideal.mem_sInf.mpr
    rintro P ⟨hle, hprime⟩
    have hmP : m ∈ P := hle (Ideal.subset_span (Set.mem_singleton m))
    have hP0 : P ≠ ⊥ := by
      intro h
      exact hm0 (by simpa [h] using hmP)
    have hPmax : P.IsMaximal := hprime.isMaximal_of_ne_bot hP0
    let Q : MaximalSpectrum R := ⟨P, hPmax⟩
    exact P.mem_of_dvd (Finset.dvd_prod_of_mem r (Finset.mem_univ Q))
      (hrP Q ⟨m, hm, hmP⟩)
  obtain ⟨n, hn⟩ := Ideal.mem_radical_iff.mp hsrad
  exact ⟨n, Ideal.mem_span_singleton.mp hn⟩

/-- Every nontrivial localization of a semilocal domain of dimension at most
one is an actual localization away from a single source element. -/
theorem exists_isLocalization_away_of_semilocal_dimensionLEOne
    {R : Type u} {T : Type v} [CommRing R] [IsDomain R]
    [Finite (MaximalSpectrum R)] [Ring.KrullDimLE 1 R]
    [CommRing T] [Nontrivial T] [Algebra R T]
    (M : Submonoid R) [IsLocalization M T] :
    ∃ s ∈ M, IsLocalization.Away s T := by
  have hM : (0 : R) ∉ M := by
    intro h
    have hzero := IsLocalization.map_units T (⟨0, h⟩ : M)
    simp at hzero
  obtain ⟨s, hs, hpow⟩ := exists_single_localization_denominator M hM
  refine ⟨s, hs, IsLocalization.Away.mk s (IsLocalization.map_units T ⟨s, hs⟩) ?_ ?_⟩
  · intro x
    obtain ⟨⟨a, m⟩, ha⟩ := IsLocalization.surj M x
    obtain ⟨n, t, ht⟩ := hpow m m.property
    refine ⟨n, a * t, ?_⟩
    rw [← map_pow, ht, map_mul, ← mul_assoc, ha, map_mul]
  · intro a b hab
    obtain ⟨m, hm⟩ := IsLocalization.exists_of_eq (M := M) hab
    obtain ⟨n, t, ht⟩ := hpow m m.property
    refine ⟨n, ?_⟩
    rw [ht, mul_right_comm, hm, mul_right_comm]

/-- Once an actual returned denominator has been constructed, ordinary
localization of the inverse-image HA subring proves target atomicity.
Hereditary atomicity is used before localization, never assumed to localize. -/
theorem isAtomicDomain_of_returned_denominator
    {R : Type u} {T : Type v} [CommRing R] [IsDomain R]
    [Finite (MaximalSpectrum R)] [CommRing T] [IsDomain T] [Algebra R T]
    (hR : Factorization.IsHereditarilyAtomic R) (C : Subring T)
    (hunit : ∀ c : C, IsUnit (c : T) → IsUnit c)
    (s : R) [IsLocalization.Away s T] (hs : algebraMap R T s ∈ C)
    (hsunit : IsUnit (⟨algebraMap R T s, hs⟩ : C)) :
    Factorization.IsAtomicDomain C := by
  let A := C.comap (algebraMap R T)
  let : Finite (MaximalSpectrum A) :=
    finite_maximalSpectrum_preimage_of_unit_reflection (algebraMap R T) C hunit
  have hA : Factorization.IsHereditarilyAtomic A := hR.subring A
  let : Ring.KrullDimLE 1 A := semilocal_dimensionLE_one hA
  let := (subringPreimageMap (algebraMap R T) C).toAlgebra
  let : IsLocalization.Away (⟨s, hs⟩ : A) C :=
    subring_preimage_isLocalization_away C s hs hsunit
  exact semilocal_isAtomicDomain_localization (Submonoid.powers (⟨s, hs⟩ : A)) C
    hA.isAtomicDomain

end HereditaryAtomicity
