import HereditaryAtomicity.Pruefer
import Mathlib.RingTheory.KrullDimension.Field

/-!
# Actual overrings of Prüfer domains

Prime localizations of the specified embedded overring use LocalSubring.ofPrime and
its localization equivalence. Fraction-field transfer and the valuation-overring
dichotomy apply in the same ambient field.
-/

namespace HereditaryAtomicity

variable {K : Type*} [Field K]

/-- Every embedded overring has the same specified fraction field. -/
theorem isFractionRing_of_subring_le (R U : Subring K) [IsFractionRing R K]
    (hRU : R ≤ U) : IsFractionRing U K := by
  apply IsFractionRing.of_field
  intro z
  obtain ⟨a, b, _, hz⟩ := IsFractionRing.div_surjective R z
  exact ⟨⟨a, hRU a.property⟩, ⟨b, hRU b.property⟩, hz.symm⟩

/-- A valuation domain embedded in its fraction field defines the corresponding
actual valuation subring of that field. -/
def valuationSubringOfIsFractionRing (R : Subring K) [IsFractionRing R K]
    [ValuationRing R] : ValuationSubring K :=
  ValuationSubring.ofSubring R fun x => by
    rcases ValuationRing.isInteger_or_isInteger R x with ⟨a, ha⟩ | ⟨a, ha⟩
    · exact Or.inl (ha ▸ a.property)
    · exact Or.inr (ha ▸ a.property)

/-- Any embedded overring of a valuation domain is a valuation domain. -/
theorem valuationRing_of_subring_le (R U : Subring K) [IsFractionRing R K]
    [ValuationRing R] (hRU : R ≤ U) : ValuationRing U := by
  let V := valuationSubringOfIsFractionRing R
  let W := ValuationSubring.ofLE V U hRU
  exact inferInstanceAs (ValuationRing W)

/-- Contracting an actual prime along an inclusion induces containment of the
corresponding embedded prime localizations. -/
theorem ofPrime_comap_le (R U : Subring K) (hRU : R ≤ U)
    (Q : Ideal U) [Q.IsPrime] :
    (LocalSubring.ofPrime R (Q.comap (Subring.inclusion hRU))).toSubring ≤
      (LocalSubring.ofPrime U Q).toSubring := by
  let hRB : R ≤ (LocalSubring.ofPrime U Q).toSubring :=
    hRU.trans (LocalSubring.le_ofPrime U Q)
  apply ofPrime_le_of_isUnit R _ _ hRB
  intro s hs
  change IsUnit (algebraMap U (LocalSubring.ofPrime U Q).toSubring
    (Subring.inclusion hRU s))
  exact IsLocalization.map_units (LocalSubring.ofPrime U Q).toSubring
    (⟨Subring.inclusion hRU s, hs⟩ : Q.primeCompl)

/-- Every actual overring of a Prüfer domain is Prüfer. -/
theorem isPrueferDomain_of_subring_le (R U : Subring K) [IsFractionRing R K]
    (hRU : R ≤ U) (hR : IsPrueferDomain R) : IsPrueferDomain U := by
  intro Q hQ
  let P := Q.comap (Subring.inclusion hRU)
  let A := (LocalSubring.ofPrime R P).toSubring
  let B := (LocalSubring.ofPrime U Q).toSubring
  let : ValuationRing A :=
    valuationRing_of_ringEquiv (LocalSubring.ofPrimeEquiv R P).symm.toRingEquiv (hR P)
  let : IsFractionRing A K := isFractionRing_of_subring_le R A (LocalSubring.le_ofPrime R P)
  have hAB : A ≤ B := ofPrime_comap_le R U hRU Q
  have hB : ValuationRing B := valuationRing_of_subring_le A B hAB
  exact valuationRing_of_ringEquiv (LocalSubring.ofPrimeEquiv U Q).toRingEquiv hB

/-- Prime localization does not increase the Krull dimension of an embedded ring. -/
theorem krullDimLE_ofPrime {n : ℕ} (R : Subring K) [Ring.KrullDimLE n R]
    (P : Ideal R) [P.IsPrime] :
    Ring.KrullDimLE n (LocalSubring.ofPrime R P).toSubring := by
  apply Ring.krullDimLE_iff.mpr
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height P]
  exact Ideal.height_le_ringKrullDim_of_isPrime.trans
    (Ring.krullDimLE_iff.mp inferInstance)

/-- An overring of a valuation domain of dimension at most one still has
 dimension at most one. This includes the original ring and the whole field. -/
theorem krullDimLE_one_of_valuation_subring_le (R U : Subring K)
    [IsFractionRing R K] [ValuationRing R] [Ring.KrullDimLE 1 R]
    (hRU : R ≤ U) : Ring.KrullDimLE 1 U := by
  let V := valuationSubringOfIsFractionRing R
  let W := ValuationSubring.ofLE V U hRU
  let : Ring.KrullDimLE 1 V := inferInstanceAs (Ring.KrullDimLE 1 R)
  rcases ValuationSubring.eq_self_or_eq_top_of_le (A := V) (B := W) hRU with h | h
  · have hRUeq : R = U := congrArg ValuationSubring.toSubring h
    exact hRUeq ▸ inferInstanceAs (Ring.KrullDimLE 1 R)
  · have hU : U = ⊤ := congrArg ValuationSubring.toSubring h
    rw [hU]
    apply Ring.krullDimLE_iff.mpr
    rw [ringKrullDim_eq_of_ringEquiv (Subring.topEquiv : (⊤ : Subring K) ≃+* K),
      ringKrullDim_eq_zero_of_field]
    exact zero_le_one

/-- Every actual overring of a Prüfer domain of dimension at most one has
 dimension at most one. The Prüfer and dimension hypotheses remain separate. -/
theorem krullDimLE_one_of_pruefer_subring_le (R U : Subring K)
    [IsFractionRing R K] [Ring.KrullDimLE 1 R]
    (hRU : R ≤ U) (hR : IsPrueferDomain R) : Ring.KrullDimLE 1 U := by
  apply Ring.krullDimLE_of_isLocalization_maximal
    (fun (Q : Ideal U) _ => (LocalSubring.ofPrime U Q).toSubring)
  intro Q hQ
  let P := Q.comap (Subring.inclusion hRU)
  let A := (LocalSubring.ofPrime R P).toSubring
  let B := (LocalSubring.ofPrime U Q).toSubring
  let : ValuationRing A :=
    valuationRing_of_ringEquiv (LocalSubring.ofPrimeEquiv R P).symm.toRingEquiv (hR P)
  let : IsFractionRing A K := isFractionRing_of_subring_le R A (LocalSubring.le_ofPrime R P)
  let : Ring.KrullDimLE 1 A := krullDimLE_ofPrime R P
  exact krullDimLE_one_of_valuation_subring_le A B (ofPrime_comap_le R U hRU Q)

end HereditaryAtomicity
