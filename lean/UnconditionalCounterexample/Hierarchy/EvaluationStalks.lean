import UnconditionalCounterexample.Hierarchy.EvaluationVertical
import UnconditionalCounterexample.Hierarchy.EvaluationVerticalCutoff
import UnconditionalCounterexample.Hierarchy.HorizontalStalks

/-!
# Compact transcendental evaluation families have DVR stalks

The prime fibers are classified by evaluation on their compact sets. The
remaining maximal ideals are horizontal and their stalks are those of the
polynomial ring after inverting the nonzero integers.
-/

noncomputable section
namespace UnconditionalCounterexample.Hierarchy

open GuardSupport

theorem almostDedekind_of_ringEquiv {A B : Type*} [CommRing A] [IsDomain A]
    [CommRing B] [IsDomain B] (e : A ≃+* B) (h : IsAlmostDedekindDomain A) :
    IsAlmostDedekindDomain B := by
  intro M hM
  let : (M.comap e).IsMaximal := Ideal.comap_isMaximal_of_surjective e e.surjective
  let := h (M.comap e)
  exact IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing
    (IsLocalization.ringEquivOfRingEquiv (Localization.AtPrime (M.comap e))
      (Localization.AtPrime M) e (e.map_primeCompl_comap_eq M))

/-- The stalk at a point of a compact fiber is its actual evaluation DVR. -/
def evaluationCenterStalkEquiv (E : EvaluationFibers) (p : PrimeIndex) (hc : IsCompact (E p))
    (a : E p) (ha : Transcendental ℚ (a.val : ℚ_[p.val])) :
    Localization.AtPrime (evaluationCenter E p a) ≃+*
      EvaluationDVR.evaluationRing p.val (a.val : ℚ_[p.val]) ha :=
  verticalStalkEquiv_of_cutoff E p a ha (exists_pair_cutoff E p hc a)

theorem evaluationPolynomials_isAlmostDedekind (E : EvaluationFibers)
    (hc : ∀ p, IsCompact (E p))
    (htr : ∀ p (a : ℤ_[p.val]), a ∈ E p → Transcendental ℚ (a : ℚ_[p.val])) :
    IsAlmostDedekindDomain (evaluationPolynomials E) := by
  intro M hM
  by_cases hv : ∃ p : PrimeIndex, (p.val : evaluationPolynomials E) ∈ M
  · obtain ⟨p,hp⟩ := hv
    obtain ⟨a,rfl⟩ := exists_center_of_prime_mem E p (hc p) M hp
    exact IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing
      (evaluationCenterStalkEquiv E p (hc p) a (htr p a.val a.property)).symm
  · exact horizontal_stalk_isDVR E M (not_exists.mp hv)

/-- The specified subring of the function field is almost Dedekind. -/
theorem evaluationRing_isAlmostDedekind (E : EvaluationFibers)
    (hc : ∀ p, IsCompact (E p)) (_hne : ∀ p, (E p).Nonempty)
    (htr : ∀ p (a : ℤ_[p.val]), a ∈ E p → Transcendental ℚ (a : ℚ_[p.val])) :
    IsAlmostDedekindDomain (evaluationRing E) :=
  almostDedekind_of_ringEquiv (evaluationRingEquiv E) (evaluationPolynomials_isAlmostDedekind E hc htr)

end UnconditionalCounterexample.Hierarchy
