import HereditaryAtomicity.PrueferBezout
import Mathlib.RingTheory.ClassGroup.Basic
import Mathlib.RingTheory.LocalProperties.Basic
import Mathlib.RingTheory.Spectrum.Maximal.Topology

/-!
# Integral ideals selected by clopen components

The construction takes place in the quotient by a nonzero principal ideal.
It applies to arbitrary domains of dimension at most one, without semilocality
or normality. Invertibility follows from an actual complementary integral factor.
-/

noncomputable section
namespace HereditaryAtomicity.DVRBase
open scoped nonZeroDivisors
open Set
variable {R : Type*} [CommRing R]

/-- A comaximal integral factor of a specified principal ideal. -/
def IsComaximalFactor (d : R) (I : Ideal R) : Prop :=
  ∃ J : Ideal R, I * J = Ideal.span {d} ∧ I ⊔ J = ⊤

/-- The two-generator ideal obtained from a lift of a quotient idempotent. -/
def liftedComponent (d e : R) : Ideal R := Ideal.span {d} ⊔ Ideal.span {e}

theorem liftedComponent_comaximal (d e : R) :
    liftedComponent d e ⊔ liftedComponent d (1 - e) = ⊤ := by
  apply (Ideal.eq_top_iff_one _).mpr
  have he : e ∈ liftedComponent d e ⊔ liftedComponent d (1 - e) :=
    Ideal.mem_sup_left (Ideal.mem_sup_right (Ideal.subset_span (Set.mem_singleton _)))
  have hf : 1 - e ∈ liftedComponent d e ⊔ liftedComponent d (1 - e) :=
    Ideal.mem_sup_right (Ideal.mem_sup_right (Ideal.subset_span (Set.mem_singleton _)))
  simpa using (liftedComponent d e ⊔ liftedComponent d (1 - e)).add_mem he hf

theorem liftedComponent_mul (d e : R) (he : e * (1 - e) ∈ Ideal.span {d}) :
    liftedComponent d e * liftedComponent d (1 - e) = Ideal.span {d} := by
  apply le_antisymm
  · rw [liftedComponent, liftedComponent, Ideal.sup_mul, Ideal.mul_sup,
      Ideal.mul_sup]
    exact sup_le (sup_le Ideal.mul_le_left Ideal.mul_le_left)
      (sup_le Ideal.mul_le_right (by
        rw [Ideal.span_singleton_mul_span_singleton]
        exact (Ideal.span_singleton_le_iff_mem _).mpr he))
  · rw [← Ideal.mul_top (Ideal.span {d}), ← liftedComponent_comaximal d e,
      Ideal.mul_sup]
    apply sup_le
    · rw [mul_comm]
      exact Ideal.mul_mono le_rfl le_sup_left
    · exact Ideal.mul_mono le_sup_left le_rfl

theorem liftedComponent_isComaximalFactor (d e : R)
    (he : e * (1 - e) ∈ Ideal.span {d}) :
    IsComaximalFactor d (liftedComponent d e) :=
  ⟨liftedComponent d (1 - e), liftedComponent_mul d e he, liftedComponent_comaximal d e⟩

theorem IsComaximalFactor.isUnit [IsDomain R] {d : R} (hd : d ≠ 0)
    {I : Ideal R} (hI : IsComaximalFactor d I) :
    IsUnit (I : FractionalIdeal R⁰ (FractionRing R)) := by
  obtain ⟨J, hIJ, _⟩ := hI
  have h := congrArg (FractionalIdeal.coeIdealHom R⁰ (FractionRing R)) hIJ
  have hu : IsUnit ((Ideal.span {d} : Ideal R) : FractionalIdeal R⁰ (FractionRing R)) :=
    IsUnit.of_mul_eq_one _ (FractionalIdeal.coe_ideal_span_singleton_mul_inv (FractionRing R) hd)
  change IsUnit ((FractionalIdeal.coeIdealHom R⁰ (FractionRing R)) (Ideal.span {d})) at hu
  rw [← h, map_mul] at hu
  exact isUnit_of_mul_isUnit_left hu

theorem liftedComponent_map_of_not_mem (P : Ideal R) [P.IsPrime] (d e : R)
    (he : e ∉ P) :
    (liftedComponent d e).map (algebraMap R (Localization.AtPrime P)) = ⊤ := by
  rw [liftedComponent, Ideal.map_sup]
  have hu := (IsLocalization.AtPrime.isUnit_to_map_iff (Localization.AtPrime P) P e).mpr he
  simp [Ideal.map_span, Ideal.span_singleton_eq_top.mpr hu]

theorem liftedComponent_map_of_mem (P : Ideal R) [P.IsPrime] (d e : R)
    (hidem : e * (1 - e) ∈ Ideal.span {d}) (he : e ∈ P) :
    (liftedComponent d e).map (algebraMap R (Localization.AtPrime P)) =
      Ideal.span {algebraMap R (Localization.AtPrime P) d} := by
  have hne : 1 - e ∉ P := by
    intro hf
    have : (1 : R) ∈ P := by simpa using P.add_mem he hf
    exact (inferInstance : P.IsPrime).ne_top ((Ideal.eq_top_iff_one _).mpr this)
  have h := congrArg (Ideal.map (algebraMap R (Localization.AtPrime P)))
    (liftedComponent_mul d e hidem)
  rw [Ideal.map_mul, liftedComponent_map_of_not_mem P d (1 - e) hne,
    Ideal.mul_top] at h
  simpa [Ideal.map_span] using h


variable [IsDomain R] [Ring.KrullDimLE 1 R]

/-- The maximal ideal beneath a prime of a nonzero principal quotient. -/
def quotientMaximal (d : R) (hd : d ≠ 0)
    (P : PrimeSpectrum (R ⧸ Ideal.span {d})) : MaximalSpectrum R :=
  ⟨P.asIdeal.comap (Ideal.Quotient.mk (Ideal.span {d})), by
    apply (Ideal.comap_isPrime _ _).isMaximal_of_ne_bot
    intro hz
    have hle := Ideal.ker_le_comap (K := P.asIdeal)
      (Ideal.Quotient.mk (Ideal.span {d}))
    have hm := hle (show d ∈ RingHom.ker (Ideal.Quotient.mk (Ideal.span {d})) by
      simp only [Ideal.mk_ker]
      exact Ideal.subset_span (Set.mem_singleton d))
    exact hd (by simpa [hz] using hm)⟩

theorem quotientMaximal_continuous (d : R) (hd : d ≠ 0) :
    Continuous (quotientMaximal d hd) := by
  apply MaximalSpectrum.toPrimeSpectrum_injective.isEmbedding_induced.continuous_iff.mpr
  exact PrimeSpectrum.continuous_comap _

/-- The closed fibre of a source element, with its actual induced topology. -/
abbrev MaximalFiber (π : R) := {P : MaximalSpectrum R // π ∈ P.asIdeal}

/-- A subset of the maximal spectrum that is clopen inside a principal fibre. -/
def IsClopenInFiber (π : R) (U : Set (MaximalSpectrum R)) : Prop :=
  U ⊆ {P | π ∈ P.asIdeal} ∧
    IsClopen ((Subtype.val : MaximalFiber π → MaximalSpectrum R) ⁻¹' U)

/-- Relative clopens of one nonzero principal fibre restrict to clopens on
any other nonzero principal quotient. -/
theorem IsClopenInFiber.quotient_preimage {π d : R} {U : Set (MaximalSpectrum R)}
    (hU : IsClopenInFiber π U) (hd : d ≠ 0) :
    IsClopen (quotientMaximal d hd ⁻¹' U) := by
  let A := R ⧸ Ideal.span {d}
  let : Ring.KrullDimLE 0 A := dimension_zero_quotient_of_nonzero_ideal
    (Ideal.span {d}) (by simpa using hd)
  let s : Set (PrimeSpectrum A) := {P | π ∈ (quotientMaximal d hd P).asIdeal}
  have hs : IsClopen s := by
    convert (isClopen_basicOpen_of_dimension_zero (Ideal.Quotient.mk (Ideal.span {d}) π)).compl using 1
    ext P
    simp [s, quotientMaximal]
  let f : s → MaximalFiber π := fun P => ⟨quotientMaximal d hd P, P.property⟩
  have hf : Continuous f :=
    ((quotientMaximal_continuous d hd).comp continuous_subtype_val).subtype_mk _
  have ht := hU.2.preimage hf
  have himage : IsClopen ((Subtype.val : s → PrimeSpectrum A) ''
      (f ⁻¹' ((Subtype.val : MaximalFiber π → MaximalSpectrum R) ⁻¹' U))) :=
    ⟨hs.1.isClosedMap_subtype_val _ ht.1, hs.2.isOpenMap_subtype_val _ ht.2⟩
  convert himage using 1
  ext P
  constructor
  · intro hP
    exact ⟨⟨P, hU.1 hP⟩, hP, rfl⟩
  · rintro ⟨Q, hQ, rfl⟩
    exact hQ

/-- Exact local data of an integral component. -/
structure IsComponentIdeal (U : Set (MaximalSpectrum R)) (d : R) (I : Ideal R) : Prop where
  comaximal : IsComaximalFactor d I
  map_mem : ∀ P : MaximalSpectrum R, P ∈ U →
    I.map (algebraMap R (Localization.AtPrime P.asIdeal)) =
      Ideal.span {algebraMap R (Localization.AtPrime P.asIdeal) d}
  map_not_mem : ∀ P : MaximalSpectrum R, P ∉ U →
    I.map (algebraMap R (Localization.AtPrime P.asIdeal)) = ⊤

/-- An idempotent in the actual principal quotient constructs the integral
component and its complementary comaximal factor. -/
theorem exists_componentIdeal_of_quotient_clopen (d : R) (hd : d ≠ 0)
    (U : Set (MaximalSpectrum R)) (hU : IsClopen (quotientMaximal d hd ⁻¹' U)) :
    ∃ I : Ideal R, IsComponentIdeal U d I := by
  obtain ⟨ε, hε, hεU⟩ := PrimeSpectrum.isClopen_iff_zeroLocus.mp hU
  obtain ⟨e, he⟩ := Ideal.Quotient.mk_surjective ε
  have hidem : e * (1 - e) ∈ Ideal.span {d} := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [map_mul, map_sub, map_one, he, mul_sub, mul_one, hε.eq, sub_self]
  have hemem (P : MaximalSpectrum R) (hdP : d ∈ P.asIdeal) : e ∈ P.asIdeal ↔ P ∈ U := by
    let q := Ideal.Quotient.mk (Ideal.span {d})
    have hle : Ideal.span {d} ≤ P.asIdeal := (Ideal.span_singleton_le_iff_mem _).mpr hdP
    let Q : PrimeSpectrum (R ⧸ Ideal.span {d}) :=
      ⟨P.asIdeal.map q, Ideal.isPrime_map_quotientMk_of_isPrime hle⟩
    have hQP : quotientMaximal d hd Q = P := by
      apply MaximalSpectrum.ext
      exact Ideal.comap_map_mk hle
    have hm : ε ∈ Q.asIdeal ↔ e ∈ P.asIdeal := by
      rw [← he]
      change e ∈ (P.asIdeal.map q).comap q ↔ _
      rw [Ideal.comap_map_mk hle]
    have hmem := Set.ext_iff.mp hεU Q
    rw [Set.mem_preimage, hQP, PrimeSpectrum.mem_zeroLocus,
      Set.singleton_subset_iff] at hmem
    exact hm.symm.trans hmem.symm
  refine ⟨liftedComponent d e, liftedComponent_isComaximalFactor d e hidem, ?_, ?_⟩
  · intro P hPU
    by_cases hdP : d ∈ P.asIdeal
    · exact liftedComponent_map_of_mem P.asIdeal d e hidem ((hemem P hdP).mpr hPU)
    · have hu := (IsLocalization.AtPrime.isUnit_to_map_iff (Localization.AtPrime P.asIdeal)
        P.asIdeal d).mpr hdP
      rw [Ideal.span_singleton_eq_top.mpr hu, liftedComponent, Ideal.map_sup]
      simp [Ideal.map_span, Ideal.span_singleton_eq_top.mpr hu]
  · intro P hPU
    by_cases hdP : d ∈ P.asIdeal
    · exact liftedComponent_map_of_not_mem P.asIdeal d e
        (fun heP => hPU ((hemem P hdP).mp heP))
    · have hu := (IsLocalization.AtPrime.isUnit_to_map_iff (Localization.AtPrime P.asIdeal)
        P.asIdeal d).mpr hdP
      rw [liftedComponent, Ideal.map_sup]
      simp [Ideal.map_span, Ideal.span_singleton_eq_top.mpr hu]

/-- Every relative clopen in a principal fibre has an actual integral,
invertible component for every nonzero source element. -/
theorem exists_componentIdeal {π : R} {U : Set (MaximalSpectrum R)}
    (hU : IsClopenInFiber π U) (d : R) (hd : d ≠ 0) :
    ∃ I : Ideal R, IsComponentIdeal U d I :=
  exists_componentIdeal_of_quotient_clopen d hd U (hU.quotient_preimage hd)


omit [IsDomain R] [Ring.KrullDimLE 1 R] in
/-- Exact localizations determine the component uniquely. -/
theorem IsComponentIdeal.unique {U : Set (MaximalSpectrum R)} {d : R}
    {I J : Ideal R} (hI : IsComponentIdeal U d I) (hJ : IsComponentIdeal U d J) : I = J := by
  apply Ideal.eq_of_localization_maximal
  intro P hP
  let Q : MaximalSpectrum R := ⟨P, hP⟩
  by_cases hQ : Q ∈ U
  · exact (hI.map_mem Q hQ).trans (hJ.map_mem Q hQ).symm
  · exact (hI.map_not_mem Q hQ).trans (hJ.map_not_mem Q hQ).symm

/-- The unique integral component selected by a relative clopen. -/
def componentIdeal {π : R} {U : Set (MaximalSpectrum R)}
    (hU : IsClopenInFiber π U) (d : R) (hd : d ≠ 0) : Ideal R :=
  (exists_componentIdeal hU d hd).choose

theorem componentIdeal_spec {π : R} {U : Set (MaximalSpectrum R)}
    (hU : IsClopenInFiber π U) (d : R) (hd : d ≠ 0) :
    IsComponentIdeal U d (componentIdeal hU d hd) :=
  (exists_componentIdeal hU d hd).choose_spec

theorem componentIdeal_one {π : R} {U : Set (MaximalSpectrum R)}
    (hU : IsClopenInFiber π U) : componentIdeal hU 1 one_ne_zero = ⊤ := by
  apply Ideal.eq_of_localization_maximal
  intro P hP
  let Q : MaximalSpectrum R := ⟨P, hP⟩
  by_cases hQ : Q ∈ U
  · rw [(componentIdeal_spec hU 1 one_ne_zero).map_mem Q hQ]
    simp [Ideal.map_top]
  · rw [(componentIdeal_spec hU 1 one_ne_zero).map_not_mem Q hQ, Ideal.map_top]

/-- Components multiply exactly in the integral-ideal monoid. -/
theorem componentIdeal_mul {π : R} {U : Set (MaximalSpectrum R)}
    (hU : IsClopenInFiber π U) (a b : R) (ha : a ≠ 0) (hb : b ≠ 0) :
    componentIdeal hU (a * b) (mul_ne_zero ha hb) =
      componentIdeal hU a ha * componentIdeal hU b hb := by
  apply Ideal.eq_of_localization_maximal
  intro P hP
  let Q : MaximalSpectrum R := ⟨P, hP⟩
  rw [Ideal.map_mul]
  by_cases hQ : Q ∈ U
  · rw [(componentIdeal_spec hU _ _).map_mem Q hQ,
      (componentIdeal_spec hU a ha).map_mem Q hQ,
      (componentIdeal_spec hU b hb).map_mem Q hQ, map_mul,
      Ideal.span_singleton_mul_span_singleton]
  · rw [(componentIdeal_spec hU _ _).map_not_mem Q hQ,
      (componentIdeal_spec hU a ha).map_not_mem Q hQ,
      (componentIdeal_spec hU b hb).map_not_mem Q hQ, Ideal.top_mul]

/-- A source element that is a unit on the selected region has trivial component. -/
theorem componentIdeal_eq_top {π : R} {U : Set (MaximalSpectrum R)}
    (hU : IsClopenInFiber π U) (d : R) (hd : d ≠ 0)
    (hdU : ∀ P ∈ U, d ∉ P.asIdeal) : componentIdeal hU d hd = ⊤ := by
  apply Ideal.eq_of_localization_maximal
  intro P hP
  let Q : MaximalSpectrum R := ⟨P, hP⟩
  rw [Ideal.map_top]
  by_cases hQ : Q ∈ U
  · rw [(componentIdeal_spec hU d hd).map_mem Q hQ]
    exact Ideal.span_singleton_eq_top.mpr
      ((IsLocalization.AtPrime.isUnit_to_map_iff _ _ _).mpr (hdU Q hQ))
  · exact (componentIdeal_spec hU d hd).map_not_mem Q hQ


/-- The actual principal fibre is homeomorphic to its affine quotient spectrum. -/
def maximalFiberQuotientHomeomorph (π : R) (hπ : π ≠ 0) :
    MaximalFiber π ≃ₜ PrimeSpectrum (R ⧸ Ideal.span {π}) := by
  let q := Ideal.Quotient.mk (Ideal.span {π})
  have hle (P : MaximalFiber π) : Ideal.span {π} ≤ P.val.asIdeal :=
    (Ideal.span_singleton_le_iff_mem _).mpr P.property
  let f : MaximalFiber π → PrimeSpectrum (R ⧸ Ideal.span {π}) := fun P =>
    ⟨P.val.asIdeal.map q, Ideal.isPrime_map_quotientMk_of_isPrime (hle P)⟩
  let g : PrimeSpectrum (R ⧸ Ideal.span {π}) → MaximalFiber π := fun Q =>
    ⟨quotientMaximal π hπ Q, by
      change q π ∈ Q.asIdeal
      have hz : q π = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr
        (Ideal.subset_span (Set.mem_singleton _))
      simpa only [hz] using Q.asIdeal.zero_mem⟩
  have hgf : ∀ P, g (f P) = P := by
    intro P
    apply Subtype.ext
    apply MaximalSpectrum.ext
    exact Ideal.comap_map_mk (hle P)
  have hfg : ∀ Q, f (g Q) = Q := by
    intro Q
    apply PrimeSpectrum.ext
    exact Ideal.map_comap_of_surjective q Ideal.Quotient.mk_surjective Q.asIdeal
  refine ⟨⟨f, g, hgf, hfg⟩, ?_, ?_⟩
  · apply (PrimeSpectrum.isEmbedding_comap_of_surjective _ q
      Ideal.Quotient.mk_surjective).continuous_iff.mpr
    have heq : PrimeSpectrum.comap q ∘ f =
        MaximalSpectrum.toPrimeSpectrum ∘ Subtype.val := by
      funext P
      apply PrimeSpectrum.ext
      exact Ideal.comap_map_mk (hle P)
    rw [heq]
    exact MaximalSpectrum.toPrimeSpectrum_continuous.comp continuous_subtype_val
  · exact (quotientMaximal_continuous π hπ).subtype_mk _

/-- Every source zero locus is clopen in a nonzero principal fibre. -/
theorem isClopen_fiber_support (π : R) (hπ : π ≠ 0) (d : R) :
    IsClopen {P : MaximalFiber π | d ∈ P.val.asIdeal} := by
  let : Ring.KrullDimLE 0 (R ⧸ Ideal.span {π}) :=
    dimension_zero_quotient_of_nonzero_ideal _ (by simpa using hπ)
  let e := maximalFiberQuotientHomeomorph π hπ
  have h := (isClopen_basicOpen_of_dimension_zero (Ideal.Quotient.mk (Ideal.span {π}) d)).compl
  have heq : {P : MaximalFiber π | d ∈ P.val.asIdeal} =
      e ⁻¹' (PrimeSpectrum.basicOpen (Ideal.Quotient.mk (Ideal.span {π}) d) : Set _)ᶜ := by
    ext P
    change d ∈ P.val.asIdeal ↔ ¬ Ideal.Quotient.mk (Ideal.span {π}) d ∉
      P.val.asIdeal.map (Ideal.Quotient.mk (Ideal.span {π}))
    rw [not_not]
    change d ∈ P.val.asIdeal ↔ d ∈ (P.val.asIdeal.map
      (Ideal.Quotient.mk (Ideal.span {π}))).comap (Ideal.Quotient.mk (Ideal.span {π}))
    rw [Ideal.comap_map_mk ((Ideal.span_singleton_le_iff_mem _).mpr P.property)]
  rw [heq]
  exact h.preimage e.continuous

omit [IsDomain R] [Ring.KrullDimLE 1 R] in
theorem IsClopenInFiber.fiber (π : R) : IsClopenInFiber π {P | π ∈ P.asIdeal} := by
  refine ⟨Subset.rfl, ?_⟩
  have heq : (Subtype.val : MaximalFiber π → MaximalSpectrum R) ⁻¹'
      {P | π ∈ P.asIdeal} = Set.univ := by ext P; simp [P.property]
  rw [heq]
  exact isClopen_univ

theorem IsClopenInFiber.inter_support {π : R} {U : Set (MaximalSpectrum R)}
    (hU : IsClopenInFiber π U) (hπ : π ≠ 0) (d : R) :
    IsClopenInFiber π (U ∩ {P | d ∈ P.asIdeal}) :=
  ⟨fun _ h => hU.1 h.1, hU.2.inter (isClopen_fiber_support π hπ d)⟩

theorem IsClopenInFiber.inter_avoid {π : R} {U : Set (MaximalSpectrum R)}
    (hU : IsClopenInFiber π U) (hπ : π ≠ 0) (d : R) :
    IsClopenInFiber π (U ∩ {P | d ∉ P.asIdeal}) :=
  ⟨fun _ h => hU.1 h.1, hU.2.inter (isClopen_fiber_support π hπ d).compl⟩


/-- Local association on the selected region determines the same component. -/
theorem componentIdeal_eq_of_local_associated {π : R} {U : Set (MaximalSpectrum R)}
    (hU : IsClopenInFiber π U) (a b : R) (ha : a ≠ 0) (hb : b ≠ 0)
    (hab : ∀ P ∈ U, Associated (algebraMap R (Localization.AtPrime P.asIdeal) a)
      (algebraMap R (Localization.AtPrime P.asIdeal) b)) :
    componentIdeal hU a ha = componentIdeal hU b hb := by
  apply Ideal.eq_of_localization_maximal
  intro P hP
  let Q : MaximalSpectrum R := ⟨P, hP⟩
  by_cases hQ : Q ∈ U
  · rw [(componentIdeal_spec hU a ha).map_mem Q hQ,
      (componentIdeal_spec hU b hb).map_mem Q hQ]
    exact Ideal.span_singleton_eq_span_singleton.mpr (hab Q hQ)
  · rw [(componentIdeal_spec hU a ha).map_not_mem Q hQ,
      (componentIdeal_spec hU b hb).map_not_mem Q hQ]

/-- The multiplicative law includes literal powers of integral components. -/
theorem componentIdeal_pow {π : R} {U : Set (MaximalSpectrum R)}
    (hU : IsClopenInFiber π U) (d : R) (hd : d ≠ 0) (n : ℕ) :
    componentIdeal hU (d ^ n) (pow_ne_zero n hd) = componentIdeal hU d hd ^ n := by
  induction n with
  | zero => simp only [pow_zero, componentIdeal_one, Ideal.one_eq_top]
  | succ n ih =>
      simp only [pow_succ]
      rw [componentIdeal_mul hU (d ^ n) d (pow_ne_zero n hd) hd, ih]

/-- Nonzero principal fibres are compact. -/
theorem compactSpace_maximalFiber (π : R) (hπ : π ≠ 0) : CompactSpace (MaximalFiber π) :=
  (maximalFiberQuotientHomeomorph π hπ).symm.compactSpace

/-- Nonzero principal fibres are totally separated, with no finiteness hypothesis. -/
theorem totallySeparated_maximalFiber (π : R) (hπ : π ≠ 0) :
    TotallySeparatedSpace (MaximalFiber π) := by
  let : Ring.KrullDimLE 0 (R ⧸ Ideal.span {π}) :=
    dimension_zero_quotient_of_nonzero_ideal _ (by simpa using hπ)
  let : TotallySeparatedSpace (PrimeSpectrum (R ⧸ Ideal.span {π})) :=
    totallySeparated_primeSpectrum_of_dimension_zero
  let e := maximalFiberQuotientHomeomorph π hπ
  apply totallySeparatedSpace_iff_exists_isClopen.mpr
  intro P Q hPQ
  obtain ⟨U, hU, hP, hQ⟩ := totallySeparatedSpace_iff_exists_isClopen.mp
    (inferInstance : TotallySeparatedSpace (PrimeSpectrum (R ⧸ Ideal.span {π})))
    (e.injective.ne hPQ)
  exact ⟨e ⁻¹' U, hU.preimage e.continuous, hP, hQ⟩

end HereditaryAtomicity.DVRBase
