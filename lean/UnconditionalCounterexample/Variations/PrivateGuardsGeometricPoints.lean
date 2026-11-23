import UnconditionalCounterexample.Variations.PrivateGuardsRecovery
import Mathlib.RingTheory.AlgebraicIndependent.RankAndCardinality
import Mathlib.LinearAlgebra.Dimension.Constructions

/-! # Retained geometric points over an uncountable field

A countable-dimensional algebra over an uncountable algebraically closed
field has that field as every residue field at a maximal ideal. In the
coefficient extension of the countable rational horizontal algebra this
gives a retained point on each surviving locus, without reserving rational
or algebraic points against the auxiliary punctures.
-/

noncomputable section
namespace UnconditionalCounterexample.Variations.PrivateGuardsRecovery

open MvPolynomial MultivariateFibres MultivariateRecovery Cardinal

/-- Every prime disjoint from the denominators has a retained geometric point
when the localized coordinate algebra has countable vector-space dimension. -/
theorem retained_of_countable_rank {K σ : Type} [Field K] [IsAlgClosed K] [Uncountable K]
    (M : Submonoid (MvPolynomial σ K)) (E : Type) [CommRing E] [Algebra K E]
    [Algebra (MvPolynomial σ K) E] [IsScalarTower K (MvPolynomial σ K) E] [IsLocalization M E]
    (hcount : Module.rank K E ≤ ℵ₀) (P : Ideal (MvPolynomial σ K)) (hP : P.IsPrime)
    (hdis : Disjoint (M : Set (MvPolynomial σ K)) (P : Set (MvPolynomial σ K))) :
    ∃ u : σ → K, Retained M u ∧ P ≤ pointIdeal u := by
  let J := P.map (algebraMap (MvPolynomial σ K) E)
  have hJ : J.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint M E P hP hdis
  obtain ⟨m,hm,hle⟩ := Ideal.exists_le_maximal J hJ.ne_top
  let := hm
  let L := E ⧸ m
  let : Field L := Ideal.Quotient.field m
  let π := Ideal.Quotient.mkₐ K m
  have hsmall : Module.rank K L ≤ ℵ₀ :=
    (π.toLinearMap.rank_le_of_surjective Ideal.Quotient.mk_surjective).trans hcount
  let : Algebra.IsAlgebraic K L := by
    by_contra h
    let : Algebra.Transcendental K L := Algebra.transcendental_iff_not_isAlgebraic.mpr h
    rw [Algebra.Transcendental.rank_eq_cardinalMk] at hsmall
    exact Cardinal.aleph0_lt_mk.not_ge
      ((Cardinal.mk_le_of_injective (algebraMap K L).injective).trans hsmall)
  let ρ : L →ₐ[K] K := IsAlgClosed.lift
  let φ := (ρ.comp π).comp (IsScalarTower.toAlgHom K (MvPolynomial σ K) E)
  let u := φ ∘ X
  have he (f : MvPolynomial σ K) : eval u f = φ f := by
    simpa only [aeval_eq_eval] using (DFunLike.congr_fun (aeval_unique φ) f).symm
  refine ⟨u,?_,?_⟩
  · intro f
    rw [he]
    exact ((IsLocalization.map_units E f).map (ρ.comp π).toRingHom).ne_zero
  · intro f hf
    change eval u f = 0
    rw [he]
    change ρ (Ideal.Quotient.mk m (algebraMap _ E f)) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr (hle (Ideal.mem_map_of_mem _ hf)), map_zero]

/-- A coefficient extension of a countable rational localization has
countable rank over its new coefficient field. -/
theorem rank_of_countable_base {k K σ : Type} [Field k] [Field K] [Algebra k K]
    (M : Submonoid (MvPolynomial σ k)) (B : Type) [CommRing B] [Algebra k B]
    [Algebra (MvPolynomial σ k) B] [IsScalarTower k (MvPolynomial σ k) B] [IsLocalization M B]
    [Countable B] (E : Type) [CommRing E] [Algebra K E] [Algebra (MvPolynomial σ K) E]
    [IsScalarTower K (MvPolynomial σ K) E] [IsLocalization (M.map (map (algebraMap k K))) E] :
    Module.rank K E ≤ ℵ₀ := by
  rw [← (tensorEquiv (K := K) M B E).toLinearEquiv.rank_eq, Module.rank_baseChange, Cardinal.lift_id]
  exact (rank_le_card k B).trans Cardinal.mk_le_aleph0

end UnconditionalCounterexample.Variations.PrivateGuardsRecovery
