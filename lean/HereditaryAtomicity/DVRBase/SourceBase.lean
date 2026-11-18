import HereditaryAtomicity.ArithmeticDVR

/-!
# DVR bases with a uniformizer in the original source

A coefficient DVR can be contained in a local overring. The numerator of a uniformizer
belongs to the coefficient PID and is itself a uniformizer in the DVR.
-/

noncomputable section
namespace HereditaryAtomicity.DVRBase
variable {K : Type*} [Field K]

/-- Localizing an algebraic coefficient PID produces a DVR with a uniformizer
whose value in the ambient field belongs to that original PID. -/
theorem exists_dvr_source_uniformizer_of_pid
    (R A : Subring K) [IsLocalRing R] [IsPrincipalIdealRing A]
    (hAR : A ≤ R) [Algebra.IsAlgebraic A K] (hfield : ¬ IsField R) :
    ∃ C : Subring K, ∃ hCR : C ≤ R,
      IsDiscreteValuationRing C ∧ IsLocalHom (Subring.inclusion hCR) ∧
      Algebra.IsAlgebraic C K ∧ ∃ π : C, Irreducible π ∧ (π : K) ∈ A := by
  let P := (IsLocalRing.maximalIdeal R).comap (Subring.inclusion hAR)
  let C := (LocalSubring.ofPrime A P).toSubring
  have hs : ∀ s : P.primeCompl, IsUnit (Subring.inclusion hAR (s : A)) := by
    intro s
    simpa only [P, Ideal.mem_primeCompl_iff, Ideal.mem_comap,
      IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not] using s.property
  let f : C →+* R := IsLocalization.lift (g := Subring.inclusion hAR) hs
  have hf : R.subtype.comp f = C.subtype := by
    apply IsLocalization.ringHom_ext P.primeCompl
    ext a
    simp only [RingHom.comp_apply, IsLocalization.lift_eq, f]
    rfl
  have hCR : C ≤ R := by
    intro x hx
    have heq := DFunLike.congr_fun hf (⟨x, hx⟩ : C)
    change (f ⟨x, hx⟩ : K) = x at heq
    rw [← heq]
    exact (f ⟨x, hx⟩).property
  let : Algebra C R := (Subring.inclusion hCR).toAlgebra
  let : IsScalarTower C R K := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : Algebra.IsAlgebraic C K := Algebra.IsAlgebraic.extendScalars
    (Subring.inclusion_injective (LocalSubring.le_ofPrime A P))
  have hP : P ≠ ⊥ := by
    intro hP
    have hCfield : IsField C := by
      refine ⟨⟨0, 1, zero_ne_one⟩, mul_comm, ?_⟩
      intro x hx
      obtain ⟨a, s, rfl⟩ := IsLocalization.exists_mk'_eq P.primeCompl x
      have ha : a ≠ 0 := by intro ha; apply hx; simp [ha]
      have hu : IsUnit (IsLocalization.mk' C a s) := by
        apply (IsLocalization.AtPrime.isUnit_mk'_iff C P a s).mpr
        simpa only [hP, Ideal.mem_primeCompl_iff, Ideal.mem_bot] using ha
      exact isUnit_iff_exists_inv.mp hu
    let : Field C := hCfield.toField
    let : Algebra.IsAlgebraic C R := Algebra.IsAlgebraic.tower_bot_of_injective
      (A := K) Subtype.val_injective
    let : Algebra.IsIntegral C R := Algebra.IsAlgebraic.isIntegral
    exact hfield (isField_of_isIntegral_of_isField' hCfield)
  let : IsDiscreteValuationRing C :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain A hP C
  have hlocal : IsLocalHom (Subring.inclusion hCR) := by
    constructor
    intro x hx
    obtain ⟨⟨a, s⟩, hxs⟩ := IsLocalization.surj P.primeCompl x
    have heq : Subring.inclusion hCR x * Subring.inclusion hAR (s : A) =
        Subring.inclusion hAR a := by
      apply Subtype.ext
      exact congrArg (fun y : C => (y : K)) hxs
    have ha : IsUnit (Subring.inclusion hAR a) := heq ▸ hx.mul (hs s)
    have haP : a ∈ P.primeCompl := by
      simpa only [P, Ideal.mem_primeCompl_iff, Ideal.mem_comap,
        IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not] using ha
    have haC : IsUnit (algebraMap A C a) := IsLocalization.map_units C ⟨a, haP⟩
    exact isUnit_of_mul_isUnit_left (hxs.symm ▸ haC)

  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible C
  obtain ⟨⟨a, s⟩, has⟩ := IsLocalization.surj P.primeCompl π
  have hsC : IsUnit (algebraMap A C (s : A)) := IsLocalization.map_units C s
  have hirr : Irreducible (algebraMap A C a) := by
    rw [← has]
    exact (associated_mul_unit_left π _ hsC).irreducible_iff.mpr hπ
  refine ⟨C, hCR, inferInstance, hlocal, inferInstance, algebraMap A C a, hirr, ?_⟩
  exact a.property

/-- The arithmetic coefficient PID can be chosen inside the original source
image, before any local overring is selected. -/
theorem exists_coefficient_pid_in_source
    {D : Type*} [CommRing D] [IsDomain D] [Finite (MaximalSpectrum D)]
    (hD : Factorization.IsHereditarilyAtomic D) (hDfield : ¬ IsField D)
    (K : Type*) [Field K] [Algebra D K] [IsFractionRing D K] :
    ∃ A : Subring K, IsPrincipalIdealRing A ∧ Algebra.IsAlgebraic A K ∧
      A ≤ (algebraMap D K).range := by
  classical
  rcases CharP.char_is_prime_or_zero D (ringChar D) with hp | hp
  · let : Fact (Nat.Prime (ringChar D)) := ⟨hp⟩
    let : CharP K (ringChar D) := IsFractionRing.charP_of_isFractionRing D (ringChar D)
    let : Algebra (ZMod (ringChar D)) D := ZMod.algebra D (ringChar D)
    let : Algebra (ZMod (ringChar D)) K := ZMod.algebra K (ringChar D)
    let k := ZMod (ringChar D)
    obtain ⟨c, hc0, hc⟩ := exists_nonzero_mem_jacobson_of_semilocal_nonfield D hDfield
    let A := Algebra.adjoin k {algebraMap D K c}
    let F := IntermediateField.adjoin k {algebraMap D K c}
    let : IsPrincipalIdealRing A := adjoin_transcendental_isPrincipalIdealRing k _
      (transcendental_fractionField_jacobson k K hc0 hc)
    let : Algebra.IsAlgebraic F K := fractionField_isAlgebraic_adjoin_jacobson k hD K hc0 hc
    let : Algebra.IsAlgebraic A F :=
      IntermediateField.algebraAdjoinAdjoin.instIsAlgebraicSubtypeMemSubalgebraAdjoinAdjoin
        k {algebraMap D K c}
    let : Algebra.IsAlgebraic A K := Algebra.IsAlgebraic.trans A F K
    let : Algebra.IsAlgebraic A.toSubring K := ⟨fun x => by
      change IsAlgebraic A x
      exact Algebra.IsAlgebraic.isAlgebraic x⟩
    refine ⟨A.toSubring, inferInstance, inferInstance, ?_⟩
    exact adjoin_jacobson_le_overring k K (algebraMap D K).range
      (fun d => ⟨d, rfl⟩) c
  · let : CharP D 0 := hp ▸ inferInstance
    let : CharZero D := CharP.charP_to_charZero D
    let : CharZero K := IsFractionRing.charZero_of_isFractionRing D
    let : Algebra.IsAlgebraic ℚ K := semilocal_fractionField_isAlgebraic_rat hD K
    let : Algebra.IsAlgebraic ℤ ℚ := IsLocalization.isAlgebraic ℚ (nonZeroDivisors ℤ)
    let : Algebra.IsAlgebraic ℤ K := Algebra.IsAlgebraic.trans ℤ ℚ K
    let f : ℤ →+* K := Int.castRingHom K
    let A := f.range
    let : IsPrincipalIdealRing A := IsPrincipalIdealRing.of_surjective
      f.rangeRestrict f.rangeRestrict_surjective
    let : Algebra.IsAlgebraic A K := Algebra.IsAlgebraic.extendScalars
      (R := ℤ) (S := A) (FaithfulSMul.algebraMap_injective ℤ A)
    refine ⟨A, inferInstance, inferInstance, ?_⟩
    rintro x ⟨n, rfl⟩
    exact ⟨(n : D), by simp [f]⟩

/-- At every nonfield local overring of a nonfield semilocal HA source, a
coefficient DVR has a uniformizer lying in the original source image. HA is
assumed only of the source. -/
theorem exists_source_uniformizer_over_semilocal_ha
    {D : Type*} [CommRing D] [IsDomain D] [Finite (MaximalSpectrum D)]
    (hD : Factorization.IsHereditarilyAtomic D) (hDfield : ¬ IsField D)
    (K : Type*) [Field K] [Algebra D K] [IsFractionRing D K]
    (R : Subring K) [IsLocalRing R] (hRfield : ¬ IsField R)
    (hDR : ∀ d : D, algebraMap D K d ∈ R) :
    ∃ A : Subring K, ∃ hAR : A ≤ R,
      IsDiscreteValuationRing A ∧ IsLocalHom (Subring.inclusion hAR) ∧
      Algebra.IsAlgebraic A K ∧ ∃ π : A, Irreducible π ∧
        (π : K) ∈ (algebraMap D K).range ∧
        Subring.inclusion hAR π ∈ IsLocalRing.maximalIdeal R := by
  obtain ⟨B, hBpid, hBalg, hBD⟩ := exists_coefficient_pid_in_source hD hDfield K
  let : IsPrincipalIdealRing B := hBpid
  let : Algebra.IsAlgebraic B K := hBalg
  have hBR : B ≤ R := by
    intro b hb
    obtain ⟨d, rfl⟩ := hBD hb
    exact hDR d
  obtain ⟨A, hAR, hA, hlocal, halg, π, hπ, hπB⟩ :=
    exists_dvr_source_uniformizer_of_pid R B hBR hRfield
  let : IsLocalHom (Subring.inclusion hAR) := hlocal
  refine ⟨A, hAR, hA, hlocal, halg, π, hπ, hBD hπB, ?_⟩
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_map_iff]
  exact hπ.not_isUnit

/-- At each maximal stalk the base DVR has a uniformizer represented by a nonzero element
of the original maximal ideal. -/
theorem exists_source_uniformizer_at_maximal
    {D : Type*} [CommRing D] [IsDomain D] [Finite (MaximalSpectrum D)]
    (hD : Factorization.IsHereditarilyAtomic D) (hDfield : ¬ IsField D)
    (K : Type*) [Field K] [Algebra D K] [IsFractionRing D K]
    (M : MaximalSpectrum D) :
    let R := (Localization.subalgebra.ofField K M.asIdeal.primeCompl
      M.asIdeal.primeCompl_le_nonZeroDivisors).toSubring
    ∃ A : Subring K, ∃ hAR : A ≤ R,
      IsDiscreteValuationRing A ∧ IsLocalHom (Subring.inclusion hAR) ∧
      Algebra.IsAlgebraic A K ∧ ∃ π : A, Irreducible π ∧
        ∃ d : D, d ≠ 0 ∧ d ∈ M.asIdeal ∧ algebraMap D K d = (π : K) := by
  let R := (Localization.subalgebra.ofField K M.asIdeal.primeCompl
    M.asIdeal.primeCompl_le_nonZeroDivisors).toSubring
  let S := Localization.subalgebra.ofField K M.asIdeal.primeCompl
    M.asIdeal.primeCompl_le_nonZeroDivisors
  let : Algebra D R := inferInstanceAs (Algebra D S)
  let : IsLocalization.AtPrime R M.asIdeal :=
    inferInstanceAs (IsLocalization.AtPrime S M.asIdeal)
  let : IsLocalRing R := IsLocalization.AtPrime.isLocalRing R M.asIdeal
  change ∃ A : Subring K, ∃ hAR : A ≤ R, _
  have hRfield : ¬ IsField R := by
    intro hR
    let : Field R := hR.toField
    obtain ⟨a, haM, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
      (Ring.ne_bot_of_isMaximal_of_not_isField M.isMaximal hDfield)
    have ha : algebraMap D R a ≠ 0 :=
      (map_ne_zero_iff _ (IsLocalization.injective R
        M.asIdeal.primeCompl_le_nonZeroDivisors)).mpr ha0
    exact (IsLocalization.AtPrime.isUnit_to_map_iff R M.asIdeal a).mp
      (isUnit_iff_ne_zero.mpr ha) haM
  obtain ⟨A, hAR, hA, hlocal, halg, π, hπ, ⟨d, hd⟩, hπM⟩ :=
    exists_source_uniformizer_over_semilocal_ha hD hDfield K R hRfield
      (fun d => (Localization.subalgebra.ofField K M.asIdeal.primeCompl
        M.asIdeal.primeCompl_le_nonZeroDivisors).algebraMap_mem d)
  refine ⟨A, hAR, hA, hlocal, halg, π, hπ, d, ?_, ?_, hd⟩
  · intro hd0
    have : π = 0 := Subtype.ext (by simpa [hd0] using hd.symm)
    exact hπ.ne_zero this
  · have heq : algebraMap D R d = Subring.inclusion hAR π := Subtype.ext hd
    by_contra hdM
    have hu := (IsLocalization.AtPrime.isUnit_to_map_iff R M.asIdeal d).mpr hdM
    rw [heq] at hu
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hπM
    exact hπM hu

end HereditaryAtomicity.DVRBase
