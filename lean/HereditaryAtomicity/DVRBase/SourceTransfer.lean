import HereditaryAtomicity.DVRBase.SourceCertificateCore
import HereditaryAtomicity.DVRBase.SourceDomination
import HereditaryAtomicity.DVRBase.SelectedSourceLift
import HereditaryAtomicity.DVRBase.KernelIdeal
import HereditaryAtomicity.DVRBase.TailSelection

/-!
# Actual finite transfer for the selected source subring

Original-coefficient selected polynomial lifts and endpoint multiples share
one finite stage. Lemma N reflects their nonjunk status, and the exact
kernel theorem is the only remaining parameter of the intermediate transfer.
-/

noncomputable section
namespace HereditaryAtomicity.DVRBase
open scoped BigOperators NNReal
variable {K : Type*} [Field K] {R : Subring K}

/-- The actual selected indices retained at a finite source stage. -/
def selectedIndices (Λ : Set ℕ) (n : ℕ) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun i => i.val ∈ Λ)

@[simp] theorem mem_selectedIndices (Λ : Set ℕ) {n : ℕ} (i : Fin n) :
    i ∈ selectedIndices Λ n ↔ i.val ∈ Λ := by
  classical
  simp [selectedIndices]

namespace SourceBlockData
variable (D : SourceBlockData R)

/-- An admissible selection retains arbitrarily fresh ratios and satisfies
the admissible weight bound for every finite subset. This includes
every terminal interval satisfying the paper's infinite-tail bound, and also
allows more general cofinal selections. -/
structure AdmissibleTail (Λ : Set ℕ) : Prop where
  cofinal : ∀ N : ℕ, ∃ m, N ≤ m ∧ m ∈ Λ
  weight_budget : ∀ s : Finset ℕ, (∀ i ∈ s, i ∈ Λ) →
    2 * (∑ i ∈ s, D.weight i) ≤ D.endpointOrder 1

/-- The finite-subset factorization bound gives the precise budget used by F at every stage. -/
theorem AdmissibleTail.model_budget {Λ : Set ℕ} (hΛ : D.AdmissibleTail Λ)
    (n : ℕ) (hn : 0 < n) :
    2 * (∑ i ∈ (selectedIndices Λ n).filter (fun i => 0 < i.val), D.weight i.val) ≤
      remainingValue (fun i : Fin n => D.weight i.val) D.exponent 1 := by
  classical
  let s := (selectedIndices Λ n).filter (fun i => 0 < i.val)
  have h := hΛ.weight_budget (s.image Fin.val) (by
    rintro j hj
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
    exact (mem_selectedIndices Λ i).mp (Finset.mem_filter.mp hi).1)
  rw [Finset.sum_image (by
    intro i _ j _ hij
    exact Fin.ext hij)] at h
  rw [← D.endpointOrder_eq_remainingValue n 1 (Nat.succ_le_iff.mpr hn)]
  exact h

/-- The weights are summable by the endpoint lower bound. -/
theorem summable_weight : Summable D.weight :=
  summable_of_sum_range_le (fun i => (D.ratio_order_pos i).le) D.sum_range_weight_le

/-- The paper's infinite-sum budget implies admissibility for any cofinal
selection. The sum is over exactly the selected indices. -/
theorem admissibleTail_of_tsum (Λ : Set ℕ)
    (hcofinal : ∀ N : ℕ, ∃ m, N ≤ m ∧ m ∈ Λ)
    (hbudget : 2 * (∑' i, Λ.indicator D.weight i) ≤ D.endpointOrder 1) :
    D.AdmissibleTail Λ := by
  classical
  refine ⟨hcofinal, fun s hs => ?_⟩
  have hsum : Summable (Λ.indicator D.weight) := D.summable_weight.indicator Λ
  have hle := hsum.sum_le_tsum s (fun i _ =>
    Set.indicator_nonneg (fun j _ => (D.ratio_order_pos j).le) i)
  have heq : (∑ i ∈ s, Λ.indicator D.weight i) = ∑ i ∈ s, D.weight i := by
    apply Finset.sum_congr rfl
    intro i hi
    exact Set.indicator_of_mem (hs i hi) D.weight
  change (∑ i ∈ s, Λ.indicator D.weight i) ≤ ∑' i, Λ.indicator D.weight i at hle
  rw [heq] at hle
  exact (mul_le_mul_of_nonneg_left hle (by norm_num)).trans hbudget

/-- Every prescribed terminal interval with the factorization infinite-tail budget is
admissible; `N` corresponds to the paper's cutoff `l₀`. -/
theorem admissibleTail_Ici_of_tsum (N : ℕ)
    (hbudget : 2 * (∑' i, (Set.Ici N).indicator D.weight i) ≤ D.endpointOrder 1) :
    D.AdmissibleTail (Set.Ici N) :=
  D.admissibleTail_of_tsum (Set.Ici N) (tail_indices_cofinal N) hbudget

/-- Admissible tails exist for every source block system, independently of
any moving-basis growth or kernel hypotheses. -/
theorem exists_admissibleTail :
    ∃ N : ℕ, 1 ≤ N ∧ D.AdmissibleTail (Set.Ici N) := by
  obtain ⟨N, hN, hsmall⟩ := D.exists_small_weight_tail
  exact ⟨N, hN, tail_indices_cofinal N,
    fun s hs => (hsmall s hs).le⟩

theorem selectedFormalRing_le_modelPolynomialRing (O : Subring K) (Λ : Set ℕ)
    (hO : ∀ a : O, D.valuation (a : K) ≤ 1) (n : ℕ) :
    selectedFormalRing O Λ n ≤
      modelPolynomialRing (coefficientFractionValuation O D.valuation) (selectedIndices Λ n) := by
  apply Subring.closure_le.mpr
  intro p hp
  cases hp with
  | coefficient a =>
      apply modelPolynomialRing_constant
      change D.valuation (coefficientFractionEmbedding O (algebraMap O (FractionRing O) a)) ≤ 1
      rw [coefficientFractionEmbedding_algebraMap]
      exact hO a
  | coordinate i hi => exact modelPolynomialRing_variable _ _ i ((mem_selectedIndices Λ i).mpr hi)

theorem evaluation_formal_mem_sourceRing (O : Subring K) (π : O)
    (hπ : (π : K) = (D.uniformizer : K)) {n : ℕ} {q : Laurent (FractionRing O) n}
    (hq : q ∈ D.formalRing O π n) : D.evaluation O n q ∈ D.sourceRing O := by
  apply (D.mem_sourceRing_iff_finite_stage O _).mpr
  refine ⟨n, ?_⟩
  rw [← D.formalRing_map_evaluation O π hπ n]
  exact ⟨q, hq, rfl⟩

/-- An actual formal endpoint multiple evaluates into the actual source junk set. -/
theorem evaluation_endpoint_mul_mem_sourceJunk (O : Subring K) (π : O)
    (hπ : (π : K) = (D.uniformizer : K)) {n : ℕ} (m : ℕ) (hm : m ≤ n)
    {q : Laurent (FractionRing O) n} (hq : q ∈ D.formalRing O π n) :
    D.evaluation O n (endpointMonomial (algebraMap O (FractionRing O) π) D.exponent m * q) ∈
      D.sourceJunk O := by
  let qR : D.sourceRing O := ⟨D.evaluation O n q, D.evaluation_formal_mem_sourceRing O π hπ hq⟩
  refine ⟨D.ringEndpoint O m * qR,
    (D.sourceIdeal O).mul_mem_right qR (endpoint_mem_chainIdeal (D.ringEndpoint O) m), ?_⟩
  change (D.endpoint m : K) * D.evaluation O n q = _
  rw [map_mul, D.evaluation_endpoint O π hπ m hm]

/-- Lemma N applied to the literal selected polynomial ring. -/
theorem selectedFormal_junk_evaluation (O : Subring K) [IsDiscreteValuationRing O]
    (π : O) (hπirr : Irreducible π) (hπ : (π : K) = (D.uniformizer : K))
    (hO : ∀ a : O, D.valuation (a : K) ≤ 1) (Λ : Set ℕ) {n : ℕ}
    {p : Laurent (FractionRing O) n} (hp : p ∈ selectedFormalRing O Λ n)
    (hpj : p ∈ modelJunk (coefficientFractionValuation O D.valuation)
      (algebraMap O (FractionRing O) π) (D.modelParameters n)) :
    D.evaluation O n p ∈ D.sourceJunk O := by
  exact D.exists_sourceIdeal_evaluation_of_mem_modelJunk O π hπirr hπ hO p
    (fun β _ => selectedFormalRing_coeff O Λ hp β)
    (fun β hβ => (selectedFormalRing_term O Λ hp β hβ).2.1) hpj

/-- A selected polynomial plus an endpoint source multiple is an actual
finite source-model element. -/
theorem sourceThickening_lift_mem_modelSourceRing (O : Subring K) (π : O)
    (hπ : (π : K) = (D.uniformizer : K))
    (hO : ∀ a : O, D.valuation (a : K) ≤ 1) (Λ : Set ℕ) {n : ℕ}
    (m : ℕ) {p q : Laurent (FractionRing O) n}
    (hp : p ∈ selectedFormalRing O Λ n) (hq : q ∈ D.formalRing O π n) :
    p + endpointMonomial (algebraMap O (FractionRing O) π) D.exponent m * q ∈
      modelSourceRing (coefficientFractionValuation O D.valuation)
        (algebraMap O (FractionRing O) π) (D.modelParameters n) (selectedIndices Λ n) := by
  apply (mem_modelSourceRing _ _ _ _ _).mpr
  refine ⟨p, D.selectedFormalRing_le_modelPolynomialRing O Λ hO n hp, _, ?_, rfl⟩
  have hh := modelJunk_mul_left _ _ _ (D.formalRing_le_modelRing O π hπ hO n hq)
    (endpointMonomial_mem_modelJunk _ _ (D.modelParameters n) m)
  simpa only [modelParameters, mul_comm] using hh

/-- Outside-junk source elements have outside-junk selected/endpoint lifts;
this uses actual polynomial domination and actual source evaluation. -/
theorem sourceThickening_lift_not_mem_modelJunk (O : Subring K) [IsDiscreteValuationRing O]
    (π : O) (hπirr : Irreducible π) (hπ : (π : K) = (D.uniformizer : K))
    (hO : ∀ a : O, D.valuation (a : K) ≤ 1) (Λ : Set ℕ) {n : ℕ}
    (m : ℕ) (hm : m ≤ n) {p q : Laurent (FractionRing O) n}
    (hp : p ∈ selectedFormalRing O Λ n) (hq : q ∈ D.formalRing O π n)
    (hnot : D.evaluation O n
      (p + endpointMonomial (algebraMap O (FractionRing O) π) D.exponent m * q) ∉ D.sourceJunk O) :
    p + endpointMonomial (algebraMap O (FractionRing O) π) D.exponent m * q ∉
      modelJunk (coefficientFractionValuation O D.valuation)
        (algebraMap O (FractionRing O) π) (D.modelParameters n) := by
  intro hj
  have hqj : endpointMonomial (algebraMap O (FractionRing O) π) D.exponent m * q ∈
      modelJunk (coefficientFractionValuation O D.valuation)
        (algebraMap O (FractionRing O) π) (D.modelParameters n) := by
    have hh := modelJunk_mul_left _ _ _ (D.formalRing_le_modelRing O π hπ hO n hq)
      (endpointMonomial_mem_modelJunk _ _ (D.modelParameters n) m)
    simpa only [modelParameters, mul_comm] using hh
  have hpj : p ∈ modelJunk (coefficientFractionValuation O D.valuation)
      (algebraMap O (FractionRing O) π) (D.modelParameters n) := by
    simpa using (modelJunk _ _ _).sub_mem hj hqj
  apply hnot
  rw [map_add]
  exact (D.sourceJunk O).add_mem (D.selectedFormal_junk_evaluation O π hπirr hπ hO Λ hp hpj)
    (D.evaluation_endpoint_mul_mem_sourceJunk O π hπ m hm hq)

/-- Actual finite-stage transfer from Lemmas N and X. The sole kernel-control
hypothesis is discharged by Construction B in the final certificate theorem. -/
theorem noOutsideJunkFactorization_of_kernel (O : Subring K) [IsDiscreteValuationRing O]
    (π : O) (hπirr : Irreducible π) (hπ : (π : K) = (D.uniformizer : K))
    (hO : ∀ a : O, D.valuation (a : K) ≤ 1) (Λ : Set ℕ)
    (hbudget : ∀ n, 0 < n →
      2 * (∑ i ∈ (selectedIndices Λ n).filter (fun i => 0 < i.val), D.weight i.val) ≤
        remainingValue (fun i : Fin n => D.weight i.val) D.exponent 1)
    (hkernel : ∀ n, 0 < n → ∀ f : Laurent (FractionRing O) n,
      f ∈ D.formalRing O π n → D.evaluation O n f = 0 →
        f ∈ modelKernelJunk (coefficientFractionValuation O D.valuation)
          (algebraMap O (FractionRing O) π) (D.modelParameters n)) :
    D.NoOutsideJunkFactorization O Λ := by
  classical
  intro r f hf hnj hprod
  choose x hx heval using hf
  obtain ⟨N, hN⟩ := D.exists_common_sourceThickening_lifts O π hπ Λ Finset.univ x
    (fun i _ => hx i)
  let n := max 1 N
  have hn : 0 < n := by dsimp [n]; omega
  have hNn : N ≤ n := le_max_right _ _
  choose m hm p hp q hq hev using fun i => hN n hNn i (Finset.mem_univ i)
  let Φ : Fin r → Laurent (FractionRing O) n := fun i =>
    p i + endpointMonomial (algebraMap O (FractionRing O) π) D.exponent (m i) * q i
  have hΦformal : ∀ i, Φ i ∈ D.formalRing O π n := by
    intro i
    exact (D.formalRing O π n).add_mem (D.selectedFormalRing_le_formalRing O π Λ n (hp i))
      ((D.formalRing O π n).mul_mem
        (Subring.subset_closure (SourceBlockData.FormalGenerator.endpoint (m i) (hm i))) (hq i))
  have hΦeval : ∀ i, D.evaluation O n (Φ i) = f i := fun i => (hev i).trans (heval i)
  have hzero : D.evaluation O n
      ((∏ i, Φ i) - endpointMonomial (algebraMap O (FractionRing O) π) D.exponent 1) = 0 := by
    simp only [map_sub, map_prod, D.evaluation_endpoint O π hπ 1 (Nat.succ_le_iff.mpr hn), hΦeval]
    exact sub_eq_zero.mpr hprod
  have hmem : (∏ i, Φ i) - endpointMonomial (algebraMap O (FractionRing O) π) D.exponent 1 ∈
      D.formalRing O π n :=
    (D.formalRing O π n).sub_mem ((D.formalRing O π n).prod_mem (fun i _ => hΦformal i))
      (Subring.subset_closure (SourceBlockData.FormalGenerator.endpoint 1 (Nat.succ_le_iff.mpr hn)))
  obtain ⟨j, hj, he⟩ := (mem_modelKernelJunk _ _ _ _).mp (hkernel n hn _ hmem hzero)
  change endpointMonomial (algebraMap O (FractionRing O) π) D.exponent 1 * j =
    (∏ i, Φ i) - endpointMonomial (algebraMap O (FractionRing O) π) D.exponent 1 at he
  have heq : (∏ i, Φ i) = endpointMonomial (algebraMap O (FractionRing O) π) D.exponent 1 * (1 + j) := by
    linear_combination -he
  apply model_factorization_obstruction (coefficientFractionValuation O D.valuation)
    (algebraMap O (FractionRing O) π) (D.coefficientUniformizer_ne_zero O π hπ)
    (D.coefficientUniformizer_order O π hπ) (D.modelParameters n) hn
    (selectedIndices Λ n) (hbudget n hn) Finset.univ Φ
  · intro i _
    exact D.sourceThickening_lift_mem_modelSourceRing O π hπ hO Λ (m i) (hp i) (hq i)
  · intro i _
    apply D.sourceThickening_lift_not_mem_modelJunk O π hπirr hπ hO Λ (m i) (hm i) (hp i) (hq i)
    rw [hΦeval i]
    exact hnj i
  · exact hj
  · exact heq

/-- Transfer of the selected-tail obstruction for every prescribed admissible tail. Kernel control is
explicit here and is discharged by `source_certificate_of_growth`. -/
theorem source_certificate_of_kernel (O : Subring K) [IsDiscreteValuationRing O]
    (π : O) (hπirr : Irreducible π) (hπ : (π : K) = (D.uniformizer : K))
    (hO : ∀ a : O, D.valuation (a : K) ≤ 1)
    (Λ : Set ℕ) (hΛ : D.AdmissibleTail Λ)
    (hkernel : ∀ n, 0 < n → ∀ f : Laurent (FractionRing O) n,
      f ∈ D.formalRing O π n → D.evaluation O n f = 0 →
        f ∈ modelKernelJunk (coefficientFractionValuation O D.valuation)
          (algebraMap O (FractionRing O) π) (D.modelParameters n)) :
    D.NoOutsideJunkFactorization O Λ ∧
      ¬ Factorization.IsAtomicDomain (D.sourceSubring O Λ) := by
  have hno := D.noOutsideJunkFactorization_of_kernel O π hπirr hπ hO Λ
    (hΛ.model_budget D) hkernel
  exact ⟨hno, D.sourceSubring_not_atomic_of_no_factorization O hO Λ hΛ.cofinal hno⟩

/-- The same cofinal tail works for every finite transfer with the stated evaluation-kernel bound. -/
theorem exists_source_certificate_of_kernel (O : Subring K) [IsDiscreteValuationRing O]
    (π : O) (hπirr : Irreducible π) (hπ : (π : K) = (D.uniformizer : K))
    (hO : ∀ a : O, D.valuation (a : K) ≤ 1)
    (hkernel : ∀ n, 0 < n → ∀ f : Laurent (FractionRing O) n,
      f ∈ D.formalRing O π n → D.evaluation O n f = 0 →
        f ∈ modelKernelJunk (coefficientFractionValuation O D.valuation)
          (algebraMap O (FractionRing O) π) (D.modelParameters n)) :
    ∃ Λ : Set ℕ, (∃ N : ℕ, 1 ≤ N ∧ Λ = Set.Ici N) ∧
      0 ∉ Λ ∧ (∀ m : ℕ, ∃ l, m ≤ l ∧ l ∈ Λ) ∧
      D.NoOutsideJunkFactorization O Λ ∧
      ¬ Factorization.IsAtomicDomain (D.sourceSubring O Λ) := by
  obtain ⟨N, hN, hΛ⟩ := D.exists_admissibleTail
  obtain ⟨hno, hnonatomic⟩ := D.source_certificate_of_kernel O π hπirr hπ hO
    (Set.Ici N) hΛ hkernel
  exact ⟨Set.Ici N, ⟨N, hN, rfl⟩, zero_not_mem_tail_indices hN, hΛ.cofinal, hno, hnonatomic⟩

end SourceBlockData
end HereditaryAtomicity.DVRBase
