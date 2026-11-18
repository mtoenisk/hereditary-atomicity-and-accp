import HereditaryAtomicity.DVRBase.ModelSource
import HereditaryAtomicity.DVRBase.GaussBounds

/-!
# The actual part outside a monomial class

The finite decomposition for the factorization obstruction uses collected
coefficients. The selection of the retained terms depends on their values.
-/

noncomputable section
namespace HereditaryAtomicity.DVRBase
open scoped BigOperators NNReal

variable {K : Type*} [Field K] {n : ℕ}

/-- The sum of the literal terms outside a prescribed monomial class. -/
def outsideTerms (v : Valuation K ℝ≥0) (M : MonomialClass n) (f : Laurent K n) :
    Laurent K n := selectTerms (fun β c => ¬ M.contains β (realValuationOrder v c)) f

theorem outsideTerms_term_not_mem (v : Valuation K ℝ≥0) (M : MonomialClass n)
    (f : Laurent K n) (β : Fin n → ℤ) (hβ : (outsideTerms v M f).coeff β ≠ 0) :
    ¬ M.contains β (realValuationOrder v ((outsideTerms v M f).coeff β)) :=
  selectTerms_satisfies _ f β hβ

/-- The discarded terms belong to the actual supported additive group. -/
theorem sub_outsideTerms_mem (v : Valuation K ℝ≥0) (M : MonomialClass n)
    (f : Laurent K n) : f - outsideTerms v M f ∈ M.supported v := by
  rw [outsideTerms, sub_selectTerms]
  apply (MonomialClass.mem_supported v M).mpr
  intro β hβ
  exact not_not.mp (selectTerms_satisfies _ f β hβ)

theorem outsideTerms_eq_zero_iff (v : Valuation K ℝ≥0) (M : MonomialClass n)
    (f : Laurent K n) : outsideTerms v M f = 0 ↔ f ∈ M.supported v := by
  classical
  constructor
  · intro h
    simpa only [h, sub_zero] using sub_outsideTerms_mem v M f
  · intro hf
    ext β
    by_cases hβ : f.coeff β = 0
    · simp [outsideTerms, hβ]
    · have hm := (MonomialClass.mem_supported v M).mp hf β hβ
      simp [outsideTerms, hm]

theorem outsideTerms_mem_supported (v : Valuation K ℝ≥0) (M N : MonomialClass n)
    {f : Laurent K n} (hf : f ∈ N.supported v) :
    outsideTerms v M f ∈ N.supported v := selectTerms_mem_supported v N _ hf

theorem laurentGaussValue_outsideTerms_le (v : Valuation K ℝ≥0)
    (u : Fin n → ℝ) (M : MonomialClass n) (f : Laurent K n) :
    laurentGaussValue v u (outsideTerms v M f) ≤ laurentGaussValue v u f :=
  laurentGaussValue_selectTerms_le v u _ f

/-- The complementary part also has no larger Gauss value. -/
theorem laurentGaussValue_sub_outsideTerms_le (v : Valuation K ℝ≥0)
    (u : Fin n → ℝ) (M : MonomialClass n) (f : Laurent K n) :
    laurentGaussValue v u (f - outsideTerms v M f) ≤ laurentGaussValue v u f := by
  rw [outsideTerms, sub_selectTerms]
  exact laurentGaussValue_selectTerms_le v u _ f

/-- The part of an actual source polynomial supported outside the endpoint ideal. -/
def nonjunkPart (v : Valuation K ℝ≥0) (P : ModelParameters n) (f : Laurent K n) :
    Laurent K n := outsideTerms v (P.ringClass.translate (fun _ => -1) P.kappa) f

theorem nonjunkPart_eq_zero_iff (v : Valuation K ℝ≥0) (π : K)
    (hπ0 : π ≠ 0) (hπ : realValuationOrder v π = 1) (P : ModelParameters n)
    (f : Laurent K n) : nonjunkPart v P f = 0 ↔ f ∈ modelJunk v π P := by
  rw [modelJunk_eq_supported v π hπ0 hπ P]
  exact outsideTerms_eq_zero_iff v _ f

theorem nonjunkPart_mem_source (v : Valuation K ℝ≥0) (π : K)
    (hπ0 : π ≠ 0) (hπ : realValuationOrder v π = 1) (P : ModelParameters n)
    (Λ : Finset (Fin n)) {f : Laurent K n} (hf : f ∈ modelSourceRing v π P Λ) :
    nonjunkPart v P f ∈ modelSourceRing v π P Λ := by
  have hs : f ∈ (sourceClass P Λ).supported v := by
    rw [← modelSourceRing_eq_supported v π hπ0 hπ P Λ]
    exact hf
  have h := outsideTerms_mem_supported v (P.ringClass.translate (fun _ => -1) P.kappa) (sourceClass P Λ) hs
  rw [← modelSourceRing_eq_supported v π hπ0 hπ P Λ] at h
  exact h

theorem nonjunkPart_term_not_mem_junk (v : Valuation K ℝ≥0) (π : K)
    (hπ0 : π ≠ 0) (hπ : realValuationOrder v π = 1) (P : ModelParameters n)
    (f : Laurent K n) (β : Fin n → ℤ) (hβ : (nonjunkPart v P f).coeff β ≠ 0) :
    AddMonoidAlgebra.single β ((nonjunkPart v P f).coeff β) ∉ modelJunk v π P := by
  rw [modelJunk_eq_supported v π hπ0 hπ P, MonomialClass.single_mem_supported]
  exact not_or.mpr ⟨hβ, outsideTerms_term_not_mem v _ f β hβ⟩

/-- The original polynomial is its actual nonjunk part plus Zₙ times an
actual model-ring element, without an arbitrary choice of polynomial lift. -/
theorem exists_modelRing_remainder (v : Valuation K ℝ≥0) (π : K)
    (hπ0 : π ≠ 0) (hπ : realValuationOrder v π = 1) (P : ModelParameters n)
    (f : Laurent K n) :
    ∃ ρ ∈ modelRing v π P,
      f = nonjunkPart v P f + terminalMonomial π P.kappa * ρ := by
  have hmem : f - nonjunkPart v P f ∈ modelJunk v π P := by
    rw [modelJunk_eq_supported v π hπ0 hπ P]
    exact sub_outsideTerms_mem v _ f
  obtain ⟨ρ, hρ, heq⟩ := (mem_modelJunk v π P _).mp hmem
  exact ⟨ρ, hρ, by rw [heq]; ring⟩

end HereditaryAtomicity.DVRBase
