import HereditaryAtomicity.DVRBase.SourceDomination

/-!
# Polynomial domination after shrinking the coefficient ring

Actual polynomial coefficients may lie in a subring B of a model DVR O. If B is closed
under division by the uniformizer up to the order of each nonzero coefficient,
polynomial members of the model ideal evaluate into the source ideal.
-/

noncomputable section
namespace HereditaryAtomicity.DVRBase
open scoped BigOperators NNReal
variable {K : Type*} [Field K]

/-- Closure under division by uniformizer powers up to the order of a nonzero coefficient. -/
def UniformizerDivisionClosed (B : Subring K) (π : B) (v : Valuation K ℝ≥0) : Prop :=
  ∀ c : B, c ≠ 0 → ∀ e : ℕ, (e : ℝ) ≤ realValuationOrder v (c : K) →
    (c : K) / (π : K) ^ e ∈ B

/-- A nonzero shrunk coefficient retains its normalized uniformizer quotient
in `B`; it need not be a unit of `B`. The integrality of the order comes from
its containing DVR `O`, and quotient membership comes solely from division closure. -/
theorem exists_normalized_coefficient_power_of_divisionClosed
    (B O : Subring K) [IsDiscreteValuationRing O] (hBO : B ≤ O)
    (π : B) (hπirr : Irreducible (Subring.inclusion hBO π))
    (v : Valuation K ℝ≥0) (hO : ∀ a : O, v (a : K) ≤ 1)
    (hnorm : realValuationOrder v (π : K) = 1)
    (hAF : UniformizerDivisionClosed B π v) (c : B) (hc : c ≠ 0) :
    ∃ (e : ℕ) (b : B), c = b * π ^ e ∧ realValuationOrder v (c : K) = e := by
  have hcO : Subring.inclusion hBO c ≠ 0 := by
    intro hz
    apply hc
    exact Subtype.ext (congrArg O.subtype hz)
  obtain ⟨e, u, _, _, hord, _⟩ :=
    exists_normalized_dvr_coefficient_power O (Subring.inclusion hBO π) hπirr v hO
      hnorm (Subring.inclusion hBO c) hcO
  change realValuationOrder v (c : K) = (e : ℝ) at hord
  have hb := hAF c hc e (le_of_eq hord.symm)
  have hp : (π : K) ≠ 0 := by
    intro hz
    apply hπirr.ne_zero
    exact Subtype.ext hz
  refine ⟨e, ⟨(c : K) / (π : K) ^ e, hb⟩, ?_, hord⟩
  apply Subtype.ext
  change (c : K) = ((c : K) / (π : K) ^ e) * (π : K) ^ e
  exact (div_mul_cancel₀ _ (pow_ne_zero e hp)).symm

namespace SourceBlockData
variable {R : Subring K} (D : SourceBlockData R)

/-- Lemma N for one coefficient in a division-closed subring of the DVR.
The actual endpoint ideal is generated over `B`, not over the larger DVR. -/
theorem sourcePolynomialTerm_mem_sourceIdeal_of_dead_shrunk
    (B O : Subring K) [IsDiscreteValuationRing O] (hBO : B ≤ O)
    (π : B) (hπirr : Irreducible (Subring.inclusion hBO π))
    (hπ : (π : K) = (D.uniformizer : K))
    (hO : ∀ c : O, D.valuation (c : K) ≤ 1)
    (hAF : UniformizerDivisionClosed B π D.valuation)
    {n : ℕ} (c : B) (μ : Fin n → ℕ)
    (hd : c ≠ 0 → ∃ k, k ≤ n ∧
      D.threshold k + remainingValue (fun i : Fin n => D.weight i.val) D.exponent k ≤
        partialValue (fun i : Fin n => D.weight i.val)
          (realValuationOrder D.valuation (c : K)) (fun i => (μ i : ℤ)) k) :
    D.sourcePolynomialTerm B c μ ∈ D.sourceIdeal B := by
  by_cases hc : c = 0
  · simp [sourcePolynomialTerm, hc]
  · have hnorm : realValuationOrder D.valuation (π : K) = 1 := hπ ▸ D.normalized
    obtain ⟨e, b, hcoeff, hord⟩ :=
      exists_normalized_coefficient_power_of_divisionClosed B O hBO π hπirr
        D.valuation hO hnorm hAF c hc
    have hdead : ∃ k, k ≤ n ∧ D.DeadAt e μ k := by
      simpa only [hord, DeadAt] using hd hc
    have hmem := D.uniformizerPowerTerm_mem_sourceIdeal B π hπ e μ hdead
    have hterm : D.sourcePolynomialTerm B c μ =
        D.coefficientToSource B b * D.sourcePolynomialTerm B (π ^ e) μ := by
      simp only [sourcePolynomialTerm, hcoeff, map_mul, mul_assoc]
    rw [hterm]
    exact (D.sourceIdeal B).mul_mem_left _ hmem

/-- A finite Laurent polynomial with coefficients in the shrunk ring and nonnegative
exponents evaluates into the source ideal when all its nonzero terms are dead. -/
theorem exists_sourceIdeal_evaluation_of_dead_terms_shrunk
    (B O : Subring K) [IsDiscreteValuationRing O] (hBO : B ≤ O)
    (π : B) (hπirr : Irreducible (Subring.inclusion hBO π))
    (hπ : (π : K) = (D.uniformizer : K))
    (hO : ∀ c : O, D.valuation (c : K) ≤ 1)
    (hAF : UniformizerDivisionClosed B π D.valuation)
    {n : ℕ} (f : Laurent (FractionRing O) n)
    (hcoeff : ∀ β, f.coeff β ≠ 0 → ∃ c : B, algebraMap O (FractionRing O) (Subring.inclusion hBO c) = f.coeff β)
    (hnonneg : ∀ β, f.coeff β ≠ 0 → ∀ i, 0 ≤ β i)
    (hdead : ∀ β, f.coeff β ≠ 0 → ∃ k, k ≤ n ∧
      D.threshold k + remainingValue (fun i : Fin n => D.weight i.val) D.exponent k ≤
        partialValue (fun i : Fin n => D.weight i.val)
          (realValuationOrder (coefficientFractionValuation O D.valuation) (f.coeff β)) β k) :
    ∃ x : D.sourceRing B, x ∈ D.sourceIdeal B ∧ (x : K) = D.evaluation O n f := by
  classical
  have hcoeff' : ∀ β, ∃ c : B, algebraMap O (FractionRing O) (Subring.inclusion hBO c) = f.coeff β := by
    intro β
    by_cases hβ : f.coeff β = 0
    · exact ⟨0, by simp [hβ]⟩
    · exact hcoeff β hβ
  choose c hc using hcoeff'
  let x := ∑ β ∈ f.coeff.support,
    D.sourcePolynomialTerm B (c β) (fun i => (β i).toNat)
  refine ⟨x, ?_, ?_⟩
  · apply (D.sourceIdeal B).sum_mem
    intro β hβ
    have hβ0 : f.coeff β ≠ 0 := Finsupp.mem_support_iff.mp hβ
    have he : (fun i => ((β i).toNat : ℤ)) = β := by
      funext i
      exact Int.toNat_of_nonneg (hnonneg β hβ0 i)
    apply D.sourcePolynomialTerm_mem_sourceIdeal_of_dead_shrunk B O hBO π hπirr hπ hO hAF
    intro _
    have hord : realValuationOrder D.valuation (c β : K) =
        realValuationOrder (coefficientFractionValuation O D.valuation) (f.coeff β) := by
      rw [← hc β]
      simp [realValuationOrder, coefficientFractionValuation]
    simpa only [hord, he] using hdead β hβ0
  · have hf := AddMonoidAlgebra.sum_coeff_single f
    change (∑ β ∈ f.coeff.support, AddMonoidAlgebra.single β (f.coeff β)) = f at hf
    change (D.sourceRing B).subtype (∑ β ∈ f.coeff.support,
      D.sourcePolynomialTerm B (c β) (fun i => (β i).toNat)) = _
    rw [map_sum]
    calc
      _ = ∑ β ∈ f.coeff.support,
          D.evaluation O n (AddMonoidAlgebra.single β (f.coeff β)) := by
        apply Finset.sum_congr rfl
        intro β hβ
        have hβ0 : f.coeff β ≠ 0 := Finsupp.mem_support_iff.mp hβ
        simp only [Subring.subtype_apply, sourcePolynomialTerm_coe,
          evaluation, laurentEvaluation_single]
        rw [← hc β, coefficientFractionEmbedding_algebraMap]
        congr 1
        apply Finset.prod_congr rfl
        intro i _
        calc
          (D.ratio i.val : K) ^ (β i).toNat =
              (D.ratio i.val : K) ^ ((β i).toNat : ℤ) := (zpow_natCast _ _).symm
          _ = (D.ratio i.val : K) ^ β i := by rw [Int.toNat_of_nonneg (hnonneg β hβ0 i)]
      _ = D.evaluation O n f := by rw [← map_sum, hf]

/-- Polynomial members of the model ideal with division-closed coefficients evaluate into
the source endpoint ideal. -/
theorem exists_sourceIdeal_evaluation_of_mem_modelJunk_shrunk
    (B O : Subring K) [IsDiscreteValuationRing O] (hBO : B ≤ O)
    (π : B) (hπirr : Irreducible (Subring.inclusion hBO π))
    (hπ : (π : K) = (D.uniformizer : K))
    (hO : ∀ c : O, D.valuation (c : K) ≤ 1)
    (hAF : UniformizerDivisionClosed B π D.valuation)
    {n : ℕ} (f : Laurent (FractionRing O) n)
    (hcoeff : ∀ β, f.coeff β ≠ 0 → ∃ c : B, algebraMap O (FractionRing O) (Subring.inclusion hBO c) = f.coeff β)
    (hnonneg : ∀ β, f.coeff β ≠ 0 → ∀ i, 0 ≤ β i)
    (hf : f ∈ modelJunk (coefficientFractionValuation O D.valuation)
      (algebraMap O (FractionRing O) (Subring.inclusion hBO π)) (D.modelParameters n)) :
    ∃ x : D.sourceRing B, x ∈ D.sourceIdeal B ∧ (x : K) = D.evaluation O n f := by
  apply D.exists_sourceIdeal_evaluation_of_dead_terms_shrunk B O hBO π hπirr hπ hO hAF f hcoeff hnonneg
  intro β hβ
  have hm := modelJunk_term_meetsLevel (coefficientFractionValuation O D.valuation)
    (algebraMap O (FractionRing O) (Subring.inclusion hBO π)) (D.coefficientUniformizer_ne_zero O (Subring.inclusion hBO π) hπ)
    (D.coefficientUniformizer_order O (Subring.inclusion hBO π) hπ) (D.modelParameters n) hf β hβ
  exact (meetsLevel_endpoint_quotient_iff (D.modelParameters n).weights
    (D.modelParameters n).kappa
    (realValuationOrder (coefficientFractionValuation O D.valuation) (f.coeff β))
    (D.modelParameters n).thresholds β (hnonneg β hβ)).mp hm


end SourceBlockData
end HereditaryAtomicity.DVRBase
