import HereditaryAtomicity.DVRBase.SelectedSourceLift
import HereditaryAtomicity.DVRBase.JointFormal

/-!
# Selected polynomial lifts with shrunk coefficients

For `B ≤ O`, the polynomial coefficients remain in `B`, while the Laurent
polynomial is realized over the fraction field of the original model base `O`.
No valuation or discreteness hypothesis is required for these algebraic lifts.
-/

noncomputable section
namespace HereditaryAtomicity.DVRBase
open scoped BigOperators
variable {K : Type*} [Field K]

/-- The selected polynomial ring over `B`, realized in the original model's
coefficient fraction field. -/
def shrunkSelectedFormalRing (B O : Subring K) (hBO : B ≤ O) (Λ : Set ℕ) (n : ℕ) :
    Subring (Laurent (FractionRing O) n) :=
  (selectedFormalRing B Λ n).map (laurentMap (coefficientFractionMap hBO) n)

/-- Shrinking the coefficients gives a literal subring of the original
selected polynomial ring. -/
theorem shrunkSelectedFormalRing_le (B O : Subring K) (hBO : B ≤ O)
    (Λ : Set ℕ) (n : ℕ) :
    shrunkSelectedFormalRing B O hBO Λ n ≤ selectedFormalRing O Λ n := by
  apply Subring.map_le_iff_le_comap.mpr
  apply Subring.closure_le.mpr
  intro p hp
  change laurentMap (coefficientFractionMap hBO) n p ∈ selectedFormalRing O Λ n
  cases hp with
  | coefficient a =>
      simpa using selectedFormalRing_coefficient O Λ n (Subring.inclusion hBO a)
  | coordinate i hi => simpa using selectedFormalRing_variable O Λ i hi

/-- Every collected coefficient is still the image of an actual element of `B`. -/
theorem shrunkSelectedFormalRing_coeff (B O : Subring K) (hBO : B ≤ O)
    (Λ : Set ℕ) {n : ℕ} {p : Laurent (FractionRing O) n}
    (hp : p ∈ shrunkSelectedFormalRing B O hBO Λ n) (β : Fin n → ℤ) :
    ∃ c : B, algebraMap O (FractionRing O) (Subring.inclusion hBO c) = p.coeff β := by
  obtain ⟨q, hq, rfl⟩ := hp
  obtain ⟨c, hc⟩ := selectedFormalRing_coeff B Λ hq β
  refine ⟨c, ?_⟩
  rw [laurentMap_coeff, ← hc, coefficientFractionMap_algebraMap]

/-- Nonzero terms retain nonnegative exponents supported in the selected variables. -/
theorem shrunkSelectedFormalRing_term (B O : Subring K) (hBO : B ≤ O)
    (Λ : Set ℕ) {n : ℕ} {p : Laurent (FractionRing O) n}
    (hp : p ∈ shrunkSelectedFormalRing B O hBO Λ n) (β : Fin n → ℤ)
    (hβ : p.coeff β ≠ 0) :
    (∃ c : B, algebraMap O (FractionRing O) (Subring.inclusion hBO c) = p.coeff β) ∧
      (∀ i, 0 ≤ β i) ∧ (∀ i, i.val ∉ Λ → β i = 0) :=
  ⟨shrunkSelectedFormalRing_coeff B O hBO Λ hp β,
    (selectedFormalRing_term O Λ (shrunkSelectedFormalRing_le B O hBO Λ n hp) β hβ).2⟩

namespace SourceBlockData
variable {R : Subring K} (D : SourceBlockData R)

/-- The canonical coefficient inclusion commutes with actual source evaluation. -/
@[simp] theorem evaluation_coefficientFractionMap (B O : Subring K) (hBO : B ≤ O)
    {n : ℕ} (p : Laurent (FractionRing B) n) :
    D.evaluation O n (laurentMap (coefficientFractionMap hBO) n p) = D.evaluation B n p := by
  rw [← AddMonoidAlgebra.sum_coeff_single p, Finsupp.sum]
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro β _
  simp only [laurentMap_single, evaluation, laurentEvaluation_single,
    coefficientFractionEmbedding_map]

/-- The finite shrunk selected formal ring evaluates to exactly the actual
ring generated over `B` by the selected source ratios before that stage. -/
theorem shrunkSelectedFormalRing_map_evaluation (B O : Subring K) (hBO : B ≤ O)
    (Λ : Set ℕ) (n : ℕ) :
    (shrunkSelectedFormalRing B O hBO Λ n).map (D.evaluation O n) =
      generatedOver B (D.selectedRatiosAt Λ n) := by
  rw [shrunkSelectedFormalRing, Subring.map_map]
  have he : (D.evaluation O n).comp (laurentMap (coefficientFractionMap hBO) n) =
      D.evaluation B n := by
    apply RingHom.ext
    intro p
    exact D.evaluation_coefficientFractionMap B O hBO p
  rw [he, D.selectedFormalRing_map_evaluation]

/-- Shrunk selected polynomials also belong to the full original-coefficient
formal source algebra. -/
theorem shrunkSelectedFormalRing_le_formalRing (B O : Subring K) (hBO : B ≤ O)
    (π : O) (Λ : Set ℕ) (n : ℕ) :
    shrunkSelectedFormalRing B O hBO Λ n ≤ D.formalRing O π n :=
  (shrunkSelectedFormalRing_le B O hBO Λ n).trans
    (D.selectedFormalRing_le_formalRing O π Λ n)

/-- Every selected-base element over `B` has a polynomial lift over the
original model base at every sufficiently large stage, with all coefficients
still belonging to `B`. -/
theorem exists_shrunkSelectedFormal_lift_ge (B O : Subring K) (hBO : B ≤ O)
    (Λ : Set ℕ) (b : D.sourceRing B) (hb : b ∈ D.selectedBase B Λ) :
    ∃ N : ℕ, ∀ n, N ≤ n → ∃ p : Laurent (FractionRing O) n,
      p ∈ shrunkSelectedFormalRing B O hBO Λ n ∧ D.evaluation O n p = (b : K) := by
  obtain ⟨N, hN⟩ := D.exists_selectedFormal_lift_ge B Λ b hb
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨p, hp, he⟩ := hN n hn
  refine ⟨laurentMap (coefficientFractionMap hBO) n p, ⟨p, hp, rfl⟩, ?_⟩
  rw [D.evaluation_coefficientFractionMap B O hBO, he]

end SourceBlockData
end HereditaryAtomicity.DVRBase
