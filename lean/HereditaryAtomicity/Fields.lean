import Factorization.BFInstances
import Factorization.HereditaryHierarchy
import HereditaryAtomicity.FieldCardinality
import HereditaryAtomicity.FieldValuations
import HereditaryAtomicity.FiniteValuationApproximation
import HereditaryAtomicity.HereditaryTransfer

/-!
# Hereditary bounded factorization of hereditarily atomic fields

This proves Coykendall–Gotti–Hasenauer, Corollary 4.5, using the valuation
intersection theorem and the actual finite-support fan argument. Countability,
outside DVRs, finite approximation and finite positive support are derived
from hereditary atomicity; none is assumed as a replacement for it.
-/

namespace HereditaryAtomicity

universe u

variable {K : Type u} [Field K]

/-- A fixed nonzero element has finite positive support among the proper
valuation subrings of an HA field. -/
theorem field_finite_positiveOutsideSupport
    (hK : Factorization.IsHereditarilyAtomic K) {z : K} (hz : z ≠ 0) :
    (positiveOutsideSupport (⊤ : Subring K) z).Finite := by
  let : Countable K := countable_of_hereditarilyAtomic_field hK
  exact finite_outside_nonunits_of_positive_centers (hK.subring ⊤)
    (field_hasFiniteOutsideUnitApproximation hK) z
    (fun _ hzV => ⟨z, hz, Subring.mem_top z, hzV⟩)

/-- Every hereditarily atomic field is hereditarily BF. Units and factors in
each unital subring are intrinsic to that subring. -/
theorem field_hereditarilyBF (hK : Factorization.IsHereditarilyAtomic K) :
    Factorization.IsHereditarilyBF K := by
  apply (Factorization.isHereditarilyBF_ringEquiv_iff
    (Subring.topEquiv : (⊤ : Subring K) ≃+* K)).mpr
  apply hereditarilyBF_of_finite_discrete_outside (⊤ : Subring K)
  · intro V hV
    apply field_valuationSubring_isDiscreteValuationRing hK V
    intro htop
    apply hV
    rw [htop]
    exact le_top
  · intro z hz
    exact field_finite_positiveOutsideSupport hK hz
  · exact (Factorization.isBFDomain_ringEquiv_iff
      (Subring.topEquiv : (⊤ : Subring K) ≃+* K)).mp
        (Factorization.isBFDomain_of_field K)

/-- The published equivalence: an HA field is precisely a field whose every
unital subring has bounded factorization. -/
theorem field_hereditarilyAtomic_iff_hereditarilyBF :
    Factorization.IsHereditarilyAtomic K ↔ Factorization.IsHereditarilyBF K :=
  ⟨field_hereditarilyBF, Factorization.IsHereditarilyBF.isHereditarilyAtomic⟩

/-- Every subring of an HA field also satisfies ACCP. -/
theorem field_hereditarilyACCP (hK : Factorization.IsHereditarilyAtomic K) :
    Factorization.IsHereditarilyACCP K :=
  (field_hereditarilyBF hK).isHereditarilyACCP

/-- For fields, hereditary atomicity and hereditary ACCP are equivalent. -/
theorem field_hereditarilyAtomic_iff_hereditarilyACCP :
    Factorization.IsHereditarilyAtomic K ↔ Factorization.IsHereditarilyACCP K :=
  ⟨field_hereditarilyACCP, Factorization.IsHereditarilyACCP.isHereditarilyAtomic⟩

end HereditaryAtomicity
