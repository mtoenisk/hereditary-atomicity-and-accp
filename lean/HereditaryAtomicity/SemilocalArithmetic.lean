import HereditaryAtomicity.SemilocalBasics
import HereditaryAtomicity.Transcendence
import Mathlib.Algebra.GCDMonoid.IntegrallyClosed
import Mathlib.Algebra.Group.Int.Units
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.RingTheory.PrincipalIdealDomain

/-!
# Arithmetic of semilocal hereditarily atomic domains

The CGH obstruction, combined with an inverted rational prime or a nonzero
Jacobson element, proves algebraicity of the actual fraction field.
-/

noncomputable section

namespace HereditaryAtomicity

universe u v w

/-- The inverse of a rational prime is not integral over the integers. -/
theorem not_isIntegral_rat_prime_inv {q : ℕ} (hq : q.Prime) :
    ¬ IsIntegral ℤ ((q : ℚ)⁻¹) := by
  intro hint
  obtain ⟨z, hz⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  have hmul : (q : ℤ) * z = 1 := by
    apply Int.cast_injective (α := ℚ)
    push_cast
    rw [show (z : ℚ) = (q : ℚ)⁻¹ from hz]
    exact mul_inv_cancel₀ (by exact_mod_cast hq.ne_zero)
  have hu : IsUnit (q : ℤ) := IsUnit.of_mul_eq_one z hmul
  have hqone : q = 1 := by simpa using (Int.isUnit_iff_natAbs_eq.mp hu)
  exact hq.ne_one hqone

/-- A rational-prime unit in a characteristic-zero domain has a nonintegral inverse. -/
theorem not_isIntegral_inv_prime_unit
    {R : Type u} [CommRing R] [IsDomain R] [CharZero R]
    (K : Type v) [Field K] [CharZero K] [Algebra R K] [IsFractionRing R K]
    [Algebra ℚ K] {q : ℕ} (hq : q.Prime) (hu : IsUnit (q : R)) :
    ¬ IsIntegral ℤ ((hu.unit⁻¹ : Rˣ) : R) := by
  intro hint
  have hmap : algebraMap R K ((hu.unit⁻¹ : Rˣ) : R) =
      algebraMap ℚ K ((q : ℚ)⁻¹) := by
    rw [map_units_inv, hu.unit_spec]
    simp
  have hK := map_isIntegral_int (algebraMap R K) hint
  rw [hmap] at hK
  exact not_isIntegral_rat_prime_inv hq (isIntegral_algebraMap_iff.mp hK)

/-- Algebraicity over the range of a field embedding is algebraicity over the
original field, with its given algebra structure. -/
theorem isAlgebraic_of_fieldRange
    (k : Type w) [Field k] {K : Type v} [Field K] [Algebra k K] {x : K}
    (hx : IsAlgebraic (algebraMap k K).fieldRange x) : IsAlgebraic k x := by
  exact hx.of_ringHom_of_comp_eq (algebraMap k K).rangeRestrictField
    (RingHom.id K) (algebraMap k K).rangeRestrictField_bijective.2
    Function.injective_id (by ext; rfl)

/-- A semilocal hereditarily atomic characteristic-zero domain has fraction
field algebraic over the rationals. -/
theorem semilocal_fractionField_isAlgebraic_rat
    {R : Type u} [CommRing R] [IsDomain R] [CharZero R]
    [Finite (MaximalSpectrum R)] (hR : Factorization.IsHereditarilyAtomic R)
    (K : Type v) [Field K] [CharZero K] [Algebra R K] [IsFractionRing R K]
    [Algebra ℚ K] : Algebra.IsAlgebraic ℚ K := by
  obtain ⟨q, hq, hu⟩ := exists_prime_isUnit_of_finite_maximalSpectrum R
  let u : Rˣ := hu.unit⁻¹
  have hu_nonint : ¬ IsIntegral ℤ (u : R) := not_isIntegral_inv_prime_unit K hq hu
  let F : Subfield K := (algebraMap ℚ K).fieldRange
  have huF : algebraMap R K (u : R) ∈ F := by
    refine ⟨(q : ℚ)⁻¹, ?_⟩
    dsimp [u]
    rw [map_units_inv, hu.unit_spec]
    simp
  apply isAlgebraic_fractionField_of_images ℚ (R := R) K
  intro x
  apply isAlgebraic_of_fieldRange ℚ
  exact isAlgebraic_over_subfield_of_nonintegral_unit hR (algebraMap R K)
    (IsFractionRing.injective R K) u hu_nonint F huF x

/-- A nonzero Jacobson element of a hereditarily atomic domain generates a
coefficient field over which its actual fraction field is algebraic. -/
theorem fractionField_isAlgebraic_adjoin_jacobson
    (k : Type w) [Field k] {R : Type u} [CommRing R] [IsDomain R] [Algebra k R]
    (hR : Factorization.IsHereditarilyAtomic R)
    (K : Type v) [Field K] [Algebra R K] [IsFractionRing R K]
    [Algebra k K] [IsScalarTower k R K] {c : R}
    (hc0 : c ≠ 0) (hc : c ∈ Ideal.jacobson (⊥ : Ideal R)) :
    Algebra.IsAlgebraic (IntermediateField.adjoin k {algebraMap R K c}) K := by
  let u : Rˣ := (isUnit_one_add_of_mem_jacobson hc).unit
  have hu : (u : R) = 1 + c := (isUnit_one_add_of_mem_jacobson hc).unit_spec
  have hnonint : ¬ IsIntegral ℤ (u : R) := by
    rw [hu]
    exact not_isIntegral_int_one_add_of_nonzero_mem_jacobson k hc0 hc
  let F := IntermediateField.adjoin k {algebraMap R K c}
  have huF : algebraMap R K (u : R) ∈ F.toSubfield := by
    rw [hu, map_add, map_one]
    exact F.add_mem F.one_mem (IntermediateField.subset_adjoin k _ (Set.mem_singleton _))
  apply isAlgebraic_fractionField_of_images F (R := R) K
  intro x
  exact isAlgebraic_over_subfield_of_nonintegral_unit hR (algebraMap R K)
    (IsFractionRing.injective R K) u hnonint F.toSubfield huF x

/-- The Jacobson generator remains transcendental in the actual fraction field. -/
theorem transcendental_fractionField_jacobson
    (k : Type w) [Field k] {R : Type u} [CommRing R] [IsDomain R] [Algebra k R]
    (K : Type v) [Field K] [Algebra R K] [IsFractionRing R K]
    [Algebra k K] [IsScalarTower k R K] {c : R}
    (hc0 : c ≠ 0) (hc : c ∈ Ideal.jacobson (⊥ : Ideal R)) :
    Transcendental k (algebraMap R K c) :=
  (transcendental_algebraMap_iff (IsFractionRing.injective R K)).mpr
    (transcendental_of_nonzero_mem_jacobson k hc0 hc)

/-- The arithmetic description of a semilocal nonfield over a coefficient field:
a transcendental Jacobson generator and algebraicity over its generated field. -/
theorem exists_jacobson_transcendental_fractionField_isAlgebraic
    (k : Type w) [Field k] {R : Type u} [CommRing R] [IsDomain R] [Algebra k R]
    [Finite (MaximalSpectrum R)] (hR : Factorization.IsHereditarilyAtomic R)
    (hfield : ¬ IsField R) (K : Type v) [Field K] [Algebra R K] [IsFractionRing R K]
    [Algebra k K] [IsScalarTower k R K] :
    ∃ c : R, c ≠ 0 ∧ c ∈ Ideal.jacobson (⊥ : Ideal R) ∧
      Transcendental k c ∧ Transcendental k (algebraMap R K c) ∧
      Algebra.IsAlgebraic (IntermediateField.adjoin k {algebraMap R K c}) K := by
  obtain ⟨c, hc0, hc⟩ := exists_nonzero_mem_jacobson_of_semilocal_nonfield R hfield
  exact ⟨c, hc0, hc, transcendental_of_nonzero_mem_jacobson k hc0 hc,
    transcendental_fractionField_jacobson k K hc0 hc,
    fractionField_isAlgebraic_adjoin_jacobson k hR K hc0 hc⟩

open scoped IntermediateField.algebraAdjoinAdjoin in
/-- The fraction field has transcendence degree exactly one over any coefficient
field whenever the domain has a nonzero Jacobson element. -/
theorem fractionField_trdeg_eq_one_of_nonzero_jacobson
    (k : Type w) [Field k] {R : Type u} [CommRing R] [IsDomain R] [Algebra k R]
    (hR : Factorization.IsHereditarilyAtomic R)
    (K : Type v) [Field K] [Algebra R K] [IsFractionRing R K]
    [Algebra k K] [IsScalarTower k R K] {c : R}
    (hc0 : c ≠ 0) (hc : c ∈ Ideal.jacobson (⊥ : Ideal R)) :
    Algebra.trdeg k K = 1 := by
  let F := IntermediateField.adjoin k {algebraMap R K c}
  let A := Algebra.adjoin k {algebraMap R K c}
  let : Algebra.IsAlgebraic F K := fractionField_isAlgebraic_adjoin_jacobson k hR K hc0 hc
  let : Algebra.IsAlgebraic A F := by
    change Algebra.IsAlgebraic (Algebra.adjoin k {algebraMap R K c})
      (IntermediateField.adjoin k {algebraMap R K c})
    exact IntermediateField.algebraAdjoinAdjoin.instIsAlgebraicSubtypeMemSubalgebraAdjoinAdjoin
      k {algebraMap R K c}
  let : Algebra.IsAlgebraic A K := Algebra.IsAlgebraic.trans A F K
  apply le_antisymm
  · simpa using Algebra.IsAlgebraic.trdeg_le_cardinalMk k ({algebraMap R K c} : Set K)
  · apply Cardinal.one_le_iff_ne_zero.mpr
    intro hz
    let : Algebra.IsAlgebraic k K := trdeg_eq_zero_iff.mp hz
    exact transcendental_fractionField_jacobson k K hc0 hc
      (Algebra.IsAlgebraic.isAlgebraic _)

/-- A transcendental element generates a polynomial PID. -/
theorem adjoin_transcendental_isPrincipalIdealRing
    (k : Type*) [Field k] {K : Type*} [Field K] [Algebra k K]
    (t : K) (ht : Transcendental k t) :
    IsPrincipalIdealRing (Algebra.adjoin k {t}) := by
  exact IsPrincipalIdealRing.of_surjective
    (Polynomial.algEquivOfTranscendental k t ht).toRingHom
    (Polynomial.algEquivOfTranscendental k t ht).surjective

end HereditaryAtomicity
