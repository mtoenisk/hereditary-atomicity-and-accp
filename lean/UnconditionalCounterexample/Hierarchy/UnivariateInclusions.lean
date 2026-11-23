import UnconditionalCounterexample.Hierarchy.UnivariateSites
import UnconditionalCounterexample.Hierarchy.EvaluationRing
import UnconditionalCounterexample.Hierarchy.IntegerValued
import UnconditionalCounterexample.Variations.TwoChainConclusion
import UnconditionalCounterexample.Variations.DyadicCounterexample

/-!
# Inclusions and intrinsic factorization on the two named examples

The polynomial evaluations in each permanent fibre give the inclusion of
the evaluation ring in the same subring of the rational function field
where the square and dyadic obstructions live.
-/

noncomputable section
namespace UnconditionalCounterexample.Hierarchy

open Variations

theorem intZInK_le_evaluationRing (E : EvaluationFibers) : intZInK ≤ evaluationRing E := by
  rintro x ⟨f,hf,rfl⟩
  exact (mem_evaluationRing_iff _ _).mpr ⟨f,rfl,fun p a _ ↦ norm_eval₂_le_one_of_integerValued p.val f hf a⟩

theorem evaluationRing_le_univariate (R : Univariate.Requirements) :
    evaluationRing (evaluationSet R) ≤ Univariate.domain R := by
  intro x hx
  obtain ⟨f,rfl,hf⟩ := (mem_evaluationRing_iff _ _).mp hx
  exact polynomial_mem_univariate R f hf

theorem intZInK_le_univariate (R : Univariate.Requirements) : intZInK ≤ Univariate.domain R :=
  (intZInK_le_evaluationRing _).trans (evaluationRing_le_univariate R)

/-- The subring statement for strong atomicity applies to the whole ring, via the top equivalence. -/
theorem stronglyAtomic_of_hereditary {R : Type*} [CommRing R] [IsDomain R]
    (h : Factorization.IsHereditarilyStronglyAtomic R) : Factorization.IsStronglyAtomicDomain R := by
  let e : (⊤ : Subring R) ≃+* R := Subring.topEquiv
  have ht := h ⊤
  refine ⟨(Factorization.isAtomicDomain_ringEquiv_iff e).mpr ht.1,?_⟩
  intro a b ha hb
  have h₀ {x : R} (hx : x ≠ 0) : e.symm x ≠ 0 := (map_ne_zero_iff _ e.symm.injective).mpr hx
  obtain ⟨d,x,y,hx,hy,hxy⟩ := ht.2 _ _ (h₀ ha) (h₀ hb)
  refine ⟨e d,e x,e y,?_,?_,?_⟩
  · simpa only [RingEquiv.apply_symm_apply,map_mul] using congrArg e hx
  · simpa only [RingEquiv.apply_symm_apply,map_mul] using congrArg e hy
  · exact IsRelPrime.of_map e.symm (by simpa only [RingEquiv.symm_apply_apply] using hxy)

theorem twoChain_intZ : intZInK ≤ TwoChains.domain := intZInK_le_univariate _
theorem dyadic_intZ : intZInK ≤ DyadicCounterexample.ring := intZInK_le_univariate _

theorem twoChain_stronglyAtomic : Factorization.IsStronglyAtomicDomain TwoChains.domain :=
  stronglyAtomic_of_hereditary TwoChains.hereditarilyStronglyAtomic

theorem dyadic_atomic : Factorization.IsAtomicDomain DyadicCounterexample.ring :=
  DyadicCounterexample.hereditarilyAtomic.isAtomicDomain

end UnconditionalCounterexample.Hierarchy
