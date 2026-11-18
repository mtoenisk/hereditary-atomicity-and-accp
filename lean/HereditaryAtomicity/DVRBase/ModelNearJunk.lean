import HereditaryAtomicity.DVRBase.ModelHigh
import HereditaryAtomicity.DVRBase.ModelG3Numerics

/-!
# The near-junk ring for disjoint squarefree multipliers

Membership in U₀ is given by coefficient support. The disjoint-mask test extends from
monomials to arbitrary Laurent polynomials by checking their collected nonzero
coefficients.
-/

noncomputable section
namespace HereditaryAtomicity.DVRBase
open scoped BigOperators NNReal
variable {K : Type*} [Field K] {n : ℕ}

/-- The actual squarefree product on a chosen coordinate set. -/
def maskMonomial (X : Finset (Fin n)) : Laurent K n :=
  AddMonoidAlgebra.single (maskExponent X) 1

theorem maskMonomial_mem_modelRing (v : Valuation K ℝ≥0) (π : K)
    (P : ModelParameters n) (X : Finset (Fin n)) :
    maskMonomial X ∈ modelRing v π P :=
  modelRing_nonneg_monomial v π P _ (maskExponent_nonneg X) 1 (by simp)

/-- G3's near-junk ring for the squarefree multiplier Y_D. -/
def modelNearJunkRing (v : Valuation K ℝ≥0) (π : K)
    (hπ0 : π ≠ 0) (hπ : realValuationOrder v π = 1) (P : ModelParameters n)
    (D : Finset (Fin n)) : Subring (Laurent K n) :=
  modelNearRing v π hπ0 hπ P (maskMonomial D) (maskMonomial_mem_modelRing v π P D)

@[simp] theorem mem_modelNearJunkRing (v : Valuation K ℝ≥0) (π : K)
    (hπ0 : π ≠ 0) (hπ : realValuationOrder v π = 1) (P : ModelParameters n)
    (D : Finset (Fin n)) (f : Laurent K n) :
    f ∈ modelNearJunkRing v π hπ0 hπ P D ↔
      f ∈ modelSharpRing v π hπ0 hπ P ∧ maskMonomial D * f ∈ modelRing v π P := Iff.rfl

theorem modelNearJunk_mul_mem_modelRing (v : Valuation K ℝ≥0) (π : K)
    (hπ0 : π ≠ 0) (hπ : realValuationOrder v π = 1) (P : ModelParameters n)
    (D : Finset (Fin n)) {f : Laurent K n}
    (hf : f ∈ modelNearJunkRing v π hπ0 hπ P D) :
    maskMonomial D * f ∈ modelRing v π P := hf.2

/-- Exact coefficient support for U₀; membership can therefore be separated termwise. -/
theorem modelNearJunkRing_eq_supported (v : Valuation K ℝ≥0) (π : K)
    (hπ0 : π ≠ 0) (hπ : realValuationOrder v π = 1) (P : ModelParameters n)
    (D : Finset (Fin n)) :
    (modelNearJunkRing v π hπ0 hπ P D).toAddSubgroup =
      (P.nearClass (maskExponent D) 0).supported v := by
  simpa only [modelNearJunkRing, maskMonomial, realValuationOrder_one] using
    modelNearRing_eq_supported v π hπ0 hπ P (maskExponent D) 1 one_ne_zero
      (maskMonomial_mem_modelRing v π P D)

theorem modelNearJunk_single_iff (v : Valuation K ℝ≥0) (π : K)
    (hπ0 : π ≠ 0) (hπ : realValuationOrder v π = 1) (P : ModelParameters n)
    (D : Finset (Fin n)) (β : Fin n → ℤ) (c : K) :
    AddMonoidAlgebra.single β c ∈ modelNearJunkRing v π hπ0 hπ P D ↔
      c = 0 ∨ (P.nearClass (maskExponent D) 0).contains β (realValuationOrder v c) := by
  change AddMonoidAlgebra.single β c ∈ (modelNearJunkRing v π hπ0 hπ P D).toAddSubgroup ↔ _
  rw [modelNearJunkRing_eq_supported, MonomialClass.single_mem_supported]

/-- Lemma 6.8(b) for actual Laurent polynomials, with no assumption that L and D cover
all variables: the two ring memberships force near-junk membership. -/
theorem modelNearJunk_of_disjoint_masks (v : Valuation K ℝ≥0) (π : K)
    (hπ0 : π ≠ 0) (hπ : realValuationOrder v π = 1) (P : ModelParameters n)
    (L D : Finset (Fin n)) (hLD : Disjoint L D) (hn : 0 < n)
    (hL0 : (⟨0, hn⟩ : Fin n) ∉ L) (hD0 : (⟨0, hn⟩ : Fin n) ∉ D)
    {f : Laurent K n} (hL : maskMonomial L * f ∈ modelRing v π P)
    (hD : maskMonomial D * f ∈ modelRing v π P) :
    f ∈ modelNearJunkRing v π hπ0 hπ P D := by
  refine ⟨?_, hD⟩
  change f ∈ (modelSharpRing v π hπ0 hπ P).toAddSubgroup
  rw [modelSharpRing_eq_supported, MonomialClass.mem_supported]
  have hLs : maskMonomial L * f ∈ P.ringClass.supported v :=
    modelRing_le_supported v π hπ P hL
  have hDs : maskMonomial D * f ∈ P.ringClass.supported v :=
    modelRing_le_supported v π hπ P hD
  rw [maskMonomial, single_mul_mem_supported_iff v P.ringClass _ one_ne_zero] at hLs hDs
  intro β hβ
  have heL := (MonomialClass.mem_supported v _).mp hLs β hβ
  have heD := (MonomialClass.mem_supported v _).mp hDs β hβ
  have hL' : MeetsLevel P.weights P.kappa P.thresholds
      (β + maskExponent L) (realValuationOrder v (f.coeff β)) := by
    simpa [MonomialClass.multiplyPreimage, ModelParameters.ringClass, add_comm] using heL
  have hD' : MeetsLevel P.weights P.kappa P.thresholds
      (β + maskExponent D) (realValuationOrder v (f.coeff β)) := by
    simpa [MonomialClass.multiplyPreimage, ModelParameters.ringClass, add_comm] using heD
  rcases meetsLevel_of_disjoint_masks P β _ L D hLD hn hL0 hD0 hL' hD' with h | h
  · exact Or.inl h
  · apply Or.inr
    simpa only [MonomialClass.translate, ModelParameters.highClass, neg_zero, zero_add,
      sub_neg_eq_add, MeetsHighLevel] using h

/-- Every model-ring element is near-junk, since its chosen multiplier is in R₀. -/
theorem modelRing_le_modelNearJunkRing (v : Valuation K ℝ≥0) (π : K)
    (hπ0 : π ≠ 0) (hπ : realValuationOrder v π = 1) (P : ModelParameters n)
    (D : Finset (Fin n)) : modelRing v π P ≤ modelNearJunkRing v π hπ0 hπ P D := by
  intro f hf
  exact ⟨AddSubgroup.mem_sup_left hf,
    (modelRing v π P).mul_mem (maskMonomial_mem_modelRing v π P D) hf⟩

/-- Membership in U₀ holds exactly term by term. -/
theorem mem_modelNearJunkRing_iff_single (v : Valuation K ℝ≥0) (π : K)
    (hπ0 : π ≠ 0) (hπ : realValuationOrder v π = 1) (P : ModelParameters n)
    (D : Finset (Fin n)) (f : Laurent K n) :
    f ∈ modelNearJunkRing v π hπ0 hπ P D ↔
      ∀ β, AddMonoidAlgebra.single β (f.coeff β) ∈ modelNearJunkRing v π hπ0 hπ P D := by
  change f ∈ (modelNearJunkRing v π hπ0 hπ P D).toAddSubgroup ↔
    ∀ β, AddMonoidAlgebra.single β (f.coeff β) ∈
      (modelNearJunkRing v π hπ0 hπ P D).toAddSubgroup
  rw [modelNearJunkRing_eq_supported]
  exact MonomialClass.mem_supported_iff_single v _ f

end HereditaryAtomicity.DVRBase
