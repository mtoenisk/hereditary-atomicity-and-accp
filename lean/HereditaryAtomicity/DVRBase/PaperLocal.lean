import HereditaryAtomicity.DVRBase.LocalCertificate
import HereditaryAtomicity.FractionFieldImage

/-!
# A nonatomic subring containing a prescribed DVR

Theorem B of *Hereditary atomicity and hereditary ACCP in semilocal domains*.
-/

namespace HereditaryAtomicity.DVRBase

private theorem exists_nonatomic_intermediate_subring
    {K : Type*} [Field K] (O R : Subring K) [IsDiscreteValuationRing O]
    [IsLocalRing R] [IsFractionRing R K] [Algebra.IsAlgebraic O K]
    (hOR : O ≤ R) (hfail : ¬ WfDvdMonoid R) :
    ∃ S : Subring K, O ≤ S ∧ S ≤ R ∧ ¬ Factorization.IsAtomicDomain S := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨t, _, C, v, hnorm, hbound, _, hratio, hfloor⟩ :=
    exists_valued_uniformizerChainData_of_not_wfDvdMonoid O R hOR π hπ hfail
  obtain ⟨D, _, _, _, _, _, _, _, _, _, _, hcert⟩ :=
    C.exists_completed_source_certificate O R hOR π hπ v
      (fun z => hbound (Subring.inclusion hOR z)) hnorm hratio hfloor
  obtain ⟨N, _, hN⟩ := D.exists_admissibleTail
  obtain ⟨_, hnon, hSR, hOS, _⟩ := hcert _ hN
  exact ⟨D.sourceSubring O (Set.Ici N), hOS, hSR, hnon⟩

-- The algebra map between the fraction fields extends the given inclusion.
attribute [local instance] FractionRing.liftAlgebra

/-- If a local domain containing a specified DVR fails ACCP and its fraction
field is algebraic over that of the DVR, it has a nonatomic subring containing
that same DVR. -/
theorem exists_nonatomic_subring_containing_dvr
    {R : Type*} [CommRing R] [IsDomain R] [IsLocalRing R]
    (O : Subring R) [IsDiscreteValuationRing O]
    (halg : Algebra.IsAlgebraic (FractionRing O) (FractionRing R))
    (hfail : ¬ WfDvdMonoid R) :
    ∃ S : Subring R, O ≤ S ∧ ¬ Factorization.IsAtomicDomain S := by
  let K := FractionRing R
  let f := algebraMap R K
  have hf : Function.Injective f := IsFractionRing.injective R K
  let e := O.equivMapOfInjective f hf
  let : IsDiscreteValuationRing (O.map f) :=
    IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing e
  let : Algebra.IsAlgebraic O K := IsFractionRing.comap_isAlgebraic_iff.mpr halg
  let : Algebra.IsAlgebraic (O.map f) K :=
    Algebra.IsAlgebraic.ringHom_of_comp_eq e (RingHom.id K) e.injective
      Function.surjective_id rfl
  let : IsLocalRing f.range := (fractionImageEquiv R K).isLocalRing
  let : IsFractionRing f.range K := isFractionRing_fractionImage R K
  have hOR : O.map f ≤ f.range := by
    rintro _ ⟨z, _, rfl⟩
    exact ⟨z, rfl⟩
  obtain ⟨T, hOT, hTR, hnon⟩ := exists_nonatomic_intermediate_subring (O.map f) f.range
    hOR (fun hw => hfail (Factorization.wfDvdMonoid_of_ringEquiv (fractionImageEquiv R K) hw))
  refine ⟨T.comap f, Subring.map_le_iff_le_comap.mp hOT, ?_⟩
  intro h
  apply hnon
  rw [← Subring.map_comap_eq_self hTR]
  exact (Factorization.subring_map_isAtomicDomain_iff (T.comap f) f hf).mpr h

end HereditaryAtomicity.DVRBase
