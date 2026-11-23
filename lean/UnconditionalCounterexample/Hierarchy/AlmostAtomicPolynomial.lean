import UnconditionalCounterexample.Hierarchy.AlmostAtomicPolynomialProducts
import UnconditionalCounterexample.Hierarchy.AlmostAtomicPolynomialFactors
import UnconditionalCounterexample.Hierarchy.AlmostAtomicPolynomialWitness
import UnconditionalCounterexample.Hierarchy.IntegerValued
import UnconditionalCounterexample.Hierarchy.EvaluationStalks
import UnconditionalCounterexample.Hierarchy.StrictClasses
import Factorization.Transport

/-!
# The almost atomic, nonatomic overring inside ℚ(t)

All factorization statements refer to the same embedded ring. The quadratic
has no atomic factorization, while multiplication by the atom 2 gives the
two linear atoms at the prescribed centres.
-/

noncomputable section
namespace UnconditionalCounterexample.Hierarchy.AlmostAtomicPolynomial
open GuardSupport Factorization Polynomial

theorem ring_almost_atomic : IsAlmostAtomicDomain ring :=
  almostAtomic_of_representatives exists_irreducible_scalar

abbrev fieldRing := evaluationRing fibres
abbrev inclusion := evaluationRingEquiv fibres

theorem fieldRing_fractionRing : IsFractionRing fieldRing (RatFunc ℚ) := evaluationRing_fractionRing fibres

theorem fieldRing_contains : intZInK ≤ fieldRing := by
  rintro _ ⟨f,hf,rfl⟩
  exact ⟨f,(mem_evaluationPolynomials_iff _ _).mpr (fun p a _ => norm_eval₂_le_one_of_integerValued p.val f hf a),rfl⟩

theorem fieldRing_almost_atomic : IsAlmostAtomicDomain fieldRing := by
  intro y hy
  obtain ⟨x,rfl⟩ := inclusion.surjective y
  obtain ⟨a,ha,hax⟩ := ring_almost_atomic x (fun h => hy (h ▸ inclusion.map_zero))
  exact ⟨inclusion a,hasAtomicFactorization_map inclusion.toMulEquiv ha,
    inclusion.map_mul a x ▸ hasAtomicFactorization_map inclusion.toMulEquiv hax⟩

theorem fieldRing_not_atomic : ¬IsAtomicDomain fieldRing :=
  fun h => ring_not_atomic ((isAtomicDomain_ringEquiv_iff inclusion).mp h)

abbrev fieldParameter : fieldRing := inclusion parameter
abbrev fieldQuadratic : fieldRing := inclusion z

theorem fieldQuadratic_value : fieldQuadratic.val = RatFunc.X*(RatFunc.X-1)/2 := by
  change algebraMap ℚ[X] (RatFunc ℚ) (C (1/2) * (X * (X-1))) = _
  rw [map_mul,RatFunc.algebraMap_C,map_mul,map_sub,RatFunc.algebraMap_X,map_one]
  rw [show RatFunc.C (1/2 : ℚ) = (1/2 : RatFunc ℚ) by norm_num]
  ring

/-- The client-level witness tested inside the field-embedded ring. -/
theorem fieldQuadratic_repair :
    ¬HasAtomicFactorization fieldQuadratic ∧ Irreducible (2 : fieldRing) ∧
      Irreducible fieldParameter ∧ Irreducible (fieldParameter - 1) ∧
      2*fieldQuadratic = fieldParameter*(fieldParameter-1) ∧ HasAtomicFactorization (2*fieldQuadratic) := by
  obtain ⟨hz,h₂,h₀,h₁,he,ha⟩ := quadratic_repair
  refine ⟨fun h => hz ((hasAtomicFactorization_mulEquiv_iff inclusion.toMulEquiv z).mp h),?_,?_,?_,?_,?_⟩
  · have h : Irreducible (inclusion 2) := (MulEquiv.irreducible_iff inclusion.toMulEquiv).mpr h₂
    simpa only [map_ofNat] using h
  · exact (MulEquiv.irreducible_iff inclusion.toMulEquiv).mpr h₀
  · have h : Irreducible (inclusion (parameter - 1)) := (MulEquiv.irreducible_iff inclusion.toMulEquiv).mpr h₁
    simpa only [map_sub,map_one] using h
  · simpa only [map_mul,map_ofNat,map_sub,map_one] using congrArg inclusion he
  · have h : HasAtomicFactorization (inclusion (2*z)) := hasAtomicFactorization_map inclusion.toMulEquiv ha
    simpa only [map_mul,map_ofNat] using h

theorem fibres_compact (p : PrimeIndex) : IsCompact (fibres p) := ((Set.finite_singleton (point p true)).insert (point p false)).isCompact

theorem fibres_nonempty (p : PrimeIndex) : (fibres p).Nonempty := ⟨_,Set.mem_insert ..⟩

theorem fibres_transcendental (p : PrimeIndex) (a : ℤ_[p.val]) (ha : a ∈ fibres p) :
    Transcendental ℚ a.val := by
  rcases ha with rfl | ha
  · exact point_trans p false
  · exact Set.mem_singleton_iff.mp ha ▸ point_trans p true

theorem fieldRing_almostDedekind : IsAlmostDedekindDomain fieldRing :=
  evaluationRing_isAlmostDedekind fibres fibres_compact fibres_nonempty fibres_transcendental

/-- Example B(2) separates atomicity from almost atomicity among the specified overrings. -/
theorem witness : StrictHierarchy.Witness (fun R => IsAtomicDomain R)
    (fun R => IsAlmostAtomicDomain R) fieldRing :=
  ⟨⟨fieldRing_contains,fieldRing_almostDedekind,fieldRing_almost_atomic⟩,fieldRing_not_atomic⟩

theorem strict_inclusion :
    StrictHierarchy.rings (fun R => IsAtomicDomain R) ⊂ StrictHierarchy.rings (fun R => IsAlmostAtomicDomain R) :=
  StrictHierarchy.strictSubset_of_witness (fun _ => IsAtomicDomain.isAlmostAtomicDomain) witness

end UnconditionalCounterexample.Hierarchy.AlmostAtomicPolynomial
