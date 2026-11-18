import HereditaryAtomicity

attribute [local instance] FractionRing.liftAlgebra

/-- Testing atomicity just on the intermediate subrings containing the
specified DVR suffices to deduce ACCP in this local domain. -/
example {R : Type*} [CommRing R] [IsDomain R] [IsLocalRing R]
    (O : Subring R) [IsDiscreteValuationRing O]
    (hAlg : Algebra.IsAlgebraic (FractionRing O) (FractionRing R))
    (hIntermediate : ∀ S : Subring R, O ≤ S → Factorization.IsAtomicDomain S) :
    WfDvdMonoid R := by
  by_contra hFail
  obtain ⟨S, hOS, hNonatomic⟩ :=
    HereditaryAtomicity.DVRBase.exists_nonatomic_subring_containing_dvr O hAlg hFail
  exact hNonatomic (hIntermediate S hOS)
