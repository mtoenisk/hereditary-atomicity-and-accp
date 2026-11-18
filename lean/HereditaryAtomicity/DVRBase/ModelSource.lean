import HereditaryAtomicity.DVRBase.ModelMembership
import HereditaryAtomicity.DVRBase.ModelPolynomial

/-!
# The finite polynomial-plus-ideal source ring

The sum defining S₀ and the resulting termwise membership criterion.
-/

noncomputable section
namespace HereditaryAtomicity.DVRBase

open scoped BigOperators NNReal
variable {K : Type*} [Field K] {n : ℕ}

/-- The actual sum of the selected polynomial ring and the endpoint ideal. -/
def modelSourceRing (v : Valuation K ℝ≥0) (π : K) (P : ModelParameters n)
    (Λ : Finset (Fin n)) : Subring (Laurent K n) where
  toAddSubgroup := (modelPolynomialRing v Λ).toAddSubgroup ⊔ modelJunk v π P
  one_mem' := AddSubgroup.mem_sup_left (modelPolynomialRing v Λ).one_mem
  mul_mem' := by
    intro f g hf hg
    obtain ⟨a, ha, j, hj, rfl⟩ := AddSubgroup.mem_sup.mp hf
    obtain ⟨b, hb, k, hk, rfl⟩ := AddSubgroup.mem_sup.mp hg
    apply AddSubgroup.mem_sup.mpr
    refine ⟨a * b, (modelPolynomialRing v Λ).mul_mem ha hb,
      a * k + b * j + j * k, ?_, ?_⟩
    · apply (modelJunk v π P).add_mem
      · exact (modelJunk v π P).add_mem
          (modelJunk_mul_left v π P (modelPolynomialRing_le_modelRing v Λ π P ha) hk)
          (modelJunk_mul_left v π P (modelPolynomialRing_le_modelRing v Λ π P hb) hj)
      · exact modelJunk_mul_left v π P (modelJunk_le_modelRing v π P hj) hk
    · ring

@[simp] theorem mem_modelSourceRing (v : Valuation K ℝ≥0) (π : K) (P : ModelParameters n)
    (Λ : Finset (Fin n)) (f : Laurent K n) :
    f ∈ modelSourceRing v π P Λ ↔
      ∃ a ∈ modelPolynomialRing v Λ, ∃ j ∈ modelJunk v π P, a + j = f :=
  AddSubgroup.mem_sup

theorem modelSourceRing_le_modelRing (v : Valuation K ℝ≥0) (π : K) (P : ModelParameters n)
    (Λ : Finset (Fin n)) : modelSourceRing v π P Λ ≤ modelRing v π P := by
  intro f hf
  obtain ⟨a, ha, j, hj, rfl⟩ := (mem_modelSourceRing v π P Λ f).mp hf
  exact (modelRing v π P).add_mem (modelPolynomialRing_le_modelRing v Λ π P ha)
    (modelJunk_le_modelRing v π P hj)

theorem modelJunk_le_modelSourceRing (v : Valuation K ℝ≥0) (π : K) (P : ModelParameters n)
    (Λ : Finset (Fin n)) : modelJunk v π P ≤ (modelSourceRing v π P Λ).toAddSubgroup :=
  le_sup_right

theorem modelPolynomialRing_le_modelSourceRing (v : Valuation K ℝ≥0) (π : K)
    (P : ModelParameters n) (Λ : Finset (Fin n)) :
    modelPolynomialRing v Λ ≤ modelSourceRing v π P Λ := by
  intro f hf
  exact AddSubgroup.mem_sup_left hf

/-- The union of polynomial monomials and ideal monomials. -/
def sourceClass (P : ModelParameters n) (Λ : Finset (Fin n)) : MonomialClass n :=
  (polynomialClass Λ).union (P.ringClass.translate (fun _ => -1) P.kappa)

/-- Lemma 6.6(c): membership in the actual polynomial-plus-ideal ring is termwise. -/
theorem modelSourceRing_eq_supported (v : Valuation K ℝ≥0) (π : K)
    (hπ0 : π ≠ 0) (hπ : realValuationOrder v π = 1) (P : ModelParameters n)
    (Λ : Finset (Fin n)) :
    (modelSourceRing v π P Λ).toAddSubgroup = (sourceClass P Λ).supported v := by
  change (modelPolynomialRing v Λ).toAddSubgroup ⊔ modelJunk v π P = _
  rw [modelPolynomialRing_eq_supported, modelJunk_eq_supported v π hπ0 hπ P]
  exact (MonomialClass.supported_union v (polynomialClass Λ) _).symm

/-- A term of S₀ outside J₀ is a polynomial monomial with integral coefficient,
nonnegative exponent, and support in the selected variables. -/
theorem modelSourceRing_nonjunk_term (v : Valuation K ℝ≥0) (π : K)
    (hπ0 : π ≠ 0) (hπ : realValuationOrder v π = 1) (P : ModelParameters n)
    (Λ : Finset (Fin n)) {f : Laurent K n} (hf : f ∈ modelSourceRing v π P Λ)
    (β : Fin n → ℤ) (hβ : f.coeff β ≠ 0)
    (hj : AddMonoidAlgebra.single β (f.coeff β) ∉ modelJunk v π P) :
    0 ≤ realValuationOrder v (f.coeff β) ∧ (∀ i, 0 ≤ β i) ∧
      (∀ i, i ∉ Λ → β i = 0) := by
  have hs : f ∈ (sourceClass P Λ).supported v := by
    rw [← modelSourceRing_eq_supported v π hπ0 hπ P Λ]
    exact hf
  have h := (MonomialClass.mem_supported v (sourceClass P Λ)).mp hs β hβ
  rcases h with h | h
  · exact h
  · exfalso
    apply hj
    rw [modelJunk_eq_supported v π hπ0 hπ P]
    exact (MonomialClass.single_mem_supported v _ β _).mpr (Or.inr h)

/-- The polynomial terms outside the ideal are dead at no level. -/
theorem modelSourceRing_nonjunk_term_not_dead (v : Valuation K ℝ≥0) (π : K)
    (hπ0 : π ≠ 0) (hπ : realValuationOrder v π = 1) (P : ModelParameters n)
    (Λ : Finset (Fin n)) {f : Laurent K n} (hf : f ∈ modelSourceRing v π P Λ)
    (β : Fin n → ℤ) (hβ : f.coeff β ≠ 0)
    (hj : AddMonoidAlgebra.single β (f.coeff β) ∉ modelJunk v π P)
    (k : ℕ) (hk : k ≤ n) :
    partialValue P.weights (realValuationOrder v (f.coeff β)) β k <
      P.thresholds k + remainingValue P.weights P.kappa k := by
  have hnonneg := (modelSourceRing_nonjunk_term v π hπ0 hπ P Λ hf β hβ hj).2.1
  have hdead := (modelJunk_single_dead_iff v π hπ0 hπ P β hnonneg _ hβ).not.mp hj
  exact lt_of_not_ge (fun h => hdead ⟨k, hk, h⟩)

end HereditaryAtomicity.DVRBase
