import HereditaryAtomicity.OutsideFactorBounds

/-!
# Hereditary transfer from finite discrete outside support

These lemmas construct their factor budgets from actual valuation rings. The
geometric hypotheses remain explicit so they can be reused by the semilocal
and field endpoints independently.
-/

namespace HereditaryAtomicity

variable {K : Type*} [Field K]

theorem boundedAmbientUnitFactors_of_finite_discrete_outside
    (D : Subring K)
    (hDVR : ∀ W : ValuationSubring K, ¬ D ≤ W.toSubring → IsDiscreteValuationRing W)
    (hfinite : ∀ z : K, z ≠ 0 → (positiveOutsideSupport D z).Finite)
    (S : Subring K) (hSD : S ≤ D) (x : S) (hx : x ≠ 0) :
    Factorization.HasBoundedAmbientUnitFactors (Subring.inclusion hSD).toMonoidHom x := by
  have hz : (x : K) ≠ 0 := fun h => hx (Subtype.ext h)
  obtain ⟨bound, hb⟩ := exists_uniform_ambientUnitFactorBound_of_finite_discrete_outside
    D hDVR x hz (hfinite x hz)
  exact ⟨bound, hb S hSD x rfl⟩

/-- Actual outside DVRs of finite support turn ambient BF into hereditary BF. -/
theorem hereditarilyBF_of_finite_discrete_outside
    (D : Subring K)
    (hDVR : ∀ W : ValuationSubring K, ¬ D ≤ W.toSubring → IsDiscreteValuationRing W)
    (hfinite : ∀ z : K, z ≠ 0 → (positiveOutsideSupport D z).Finite)
    (hD : Factorization.IsBFDomain D) : Factorization.IsHereditarilyBF D := by
  intro S
  apply (Factorization.subring_map_isBFDomain_iff S D.subtype Subtype.val_injective).mp
  have hSD : S.map D.subtype ≤ D := by
    rintro y ⟨a, _, rfl⟩
    exact a.property
  exact Factorization.isBFDomain_of_boundedAmbientUnitFactors
    (Subring.inclusion hSD) (fun _ _ h => Subtype.ext (congrArg (fun a : D => (a : K)) h))
    (boundedAmbientUnitFactors_of_finite_discrete_outside D hDVR hfinite _ hSD) hD

/-- The same actual detectors turn ambient ACCP into hereditary ACCP. -/
theorem hereditarilyACCP_of_finite_discrete_outside
    (D : Subring K)
    (hDVR : ∀ W : ValuationSubring K, ¬ D ≤ W.toSubring → IsDiscreteValuationRing W)
    (hfinite : ∀ z : K, z ≠ 0 → (positiveOutsideSupport D z).Finite)
    (hD : WfDvdMonoid D) : Factorization.IsHereditarilyACCP D := by
  intro S
  apply (Factorization.subring_map_wfDvdMonoid_iff S D.subtype Subtype.val_injective).mp
  have hSD : S.map D.subtype ≤ D := by
    rintro y ⟨a, _, rfl⟩
    exact a.property
  exact Factorization.wfDvdMonoid_of_boundedAmbientUnitFactors
    (Subring.inclusion hSD) (fun _ _ h => Subtype.ext (congrArg (fun a : D => (a : K)) h))
    (boundedAmbientUnitFactors_of_finite_discrete_outside D hDVR hfinite _ hSD) hD

end HereditaryAtomicity
