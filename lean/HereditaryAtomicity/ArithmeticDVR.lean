import HereditaryAtomicity.ArithmeticCoefficients
import HereditaryAtomicity.SemilocalDimension
import Mathlib.RingTheory.LocalRing.LocalSubring

/-! Literal DVR coefficient rings obtained by localizing an arithmetic PID. -/

noncomputable section
namespace HereditaryAtomicity

variable {K : Type*} [Field K]

/-- Localization of an embedded arithmetic PID at its actual residue center
produces a DVR contained locally in the given nonfield local source. -/
theorem exists_dvr_coefficients_of_pid
    (R A : Subring K) [IsLocalRing R] [IsPrincipalIdealRing A]
    (hAR : A ≤ R) [Algebra.IsAlgebraic A K] (hfield : ¬ IsField R) :
    ∃ C : Subring K, ∃ hCR : C ≤ R,
      IsDiscreteValuationRing C ∧ IsLocalHom (Subring.inclusion hCR) ∧
      Algebra.IsAlgebraic C K := by
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
  refine ⟨C, hCR, inferInstance, ?_, inferInstance⟩
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

/-- Every nonfield local overring of a semilocal HA domain has a literal DVR
coefficient ring over which its fraction field is algebraic. -/
theorem exists_dvr_coefficients_over_semilocal_ha
    {D : Type*} [CommRing D] [IsDomain D] [Finite (MaximalSpectrum D)]
    (hD : Factorization.IsHereditarilyAtomic D) (hDfield : ¬ IsField D)
    (K : Type*) [Field K] [Algebra D K] [IsFractionRing D K]
    (R : Subring K) [IsLocalRing R] (hRfield : ¬ IsField R)
    (hDR : ∀ d : D, algebraMap D K d ∈ R) :
    ∃ A : Subring K, ∃ hAR : A ≤ R,
      IsDiscreteValuationRing A ∧ IsLocalHom (Subring.inclusion hAR) ∧
      Algebra.IsAlgebraic A K := by
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
    exact exists_dvr_coefficients_of_pid R A.toSubring
      (adjoin_jacobson_le_overring k K R hDR c) hRfield
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
    apply exists_dvr_coefficients_of_pid R A _ hRfield
    rintro x ⟨n, rfl⟩
    exact intCast_mem R n

/-- A uniformizer in the literal coefficient DVR remains a nonzero source
nonunit; its algebraic coefficient property is retained explicitly. -/
theorem exists_arithmetic_uniformizer_over_semilocal_ha
    {D : Type*} [CommRing D] [IsDomain D] [Finite (MaximalSpectrum D)]
    (hD : Factorization.IsHereditarilyAtomic D) (hDfield : ¬ IsField D)
    (K : Type*) [Field K] [Algebra D K] [IsFractionRing D K]
    (R : Subring K) [IsLocalRing R] (hRfield : ¬ IsField R)
    (hDR : ∀ d : D, algebraMap D K d ∈ R) :
    ∃ A : Subring K, ∃ hAR : A ≤ R,
      IsDiscreteValuationRing A ∧ IsLocalHom (Subring.inclusion hAR) ∧
      Algebra.IsAlgebraic A K ∧ ∃ π : A, Irreducible π ∧
        Subring.inclusion hAR π ∈ IsLocalRing.maximalIdeal R := by
  obtain ⟨A, hAR, hA, hlocal, halg⟩ :=
    exists_dvr_coefficients_over_semilocal_ha hD hDfield K R hRfield hDR
  let : IsDiscreteValuationRing A := hA
  let : IsLocalHom (Subring.inclusion hAR) := hlocal
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible A
  refine ⟨A, hAR, hA, hlocal, halg, π, hπ, ?_⟩
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_map_iff]
  exact hπ.not_isUnit

end HereditaryAtomicity
