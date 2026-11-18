import HereditaryAtomicity.DVRBase.CoefficientShrinking
import HereditaryAtomicity.DVRBase.CoefficientLift
import HereditaryAtomicity.DVRBase.SourceGrowth

/-!
# Exact junk comparison and transfer after shrinking coefficients

The model DVR remains `O`, while the literal source generators have coefficients
in a division-closed subring `B`. The intersection formula compares the additive endpoint ideals,
without extending either ideal to the ambient field.
-/

noncomputable section
namespace HereditaryAtomicity.DVRBase
open scoped BigOperators NNReal
namespace SourceBlockData
variable {K : Type*} [Field K] {R : Subring K} (D : SourceBlockData R)

/-- Enlarging the coefficient ring enlarges the literal source generator ring. -/
theorem sourceRing_mono {B O : Subring K} (hBO : B ≤ O) :
    D.sourceRing B ≤ D.sourceRing O := by
  exact sup_le_sup_right hBO _

/-- Ambient-field membership in the endpoint ideal retains a source-ring multiplier. -/
theorem mem_sourceJunk_iff_endpoint_mul (B : Subring K) (x : K) :
    x ∈ D.sourceJunk B ↔ ∃ m : ℕ, ∃ q : D.sourceRing B,
      x = (D.endpoint m : K) * (q : K) := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨m, q, hq⟩ := (mem_chainIdeal_iff (D.ringEndpoint B)
      (D.ringRatio B) (D.ring_step B) x).mp hx
    exact ⟨m, q, congrArg (D.sourceRing B).subtype hq⟩
  · rintro ⟨m, q, rfl⟩
    exact ⟨D.ringEndpoint B m * q,
      (D.sourceIdeal B).mul_mem_right q (endpoint_mem_chainIdeal _ m), rfl⟩

/-- The actual additive junk sets are monotone in the coefficient ring. -/
theorem sourceJunk_mono {B O : Subring K} (hBO : B ≤ O) :
    D.sourceJunk B ≤ D.sourceJunk O := by
  intro x hx
  obtain ⟨m, q, hq⟩ := (D.mem_sourceJunk_iff_endpoint_mul B x).mp hx
  exact (D.mem_sourceJunk_iff_endpoint_mul O x).mpr
    ⟨m, ⟨q.val, D.sourceRing_mono hBO q.property⟩, hq⟩

/-- The selected polynomial-plus-junk source ring is monotone in coefficients. -/
theorem sourceSubring_mono {B O : Subring K} (hBO : B ≤ O) (Λ : Set ℕ) :
    D.sourceSubring B Λ ≤ D.sourceSubring O Λ := by
  rintro x ⟨x, hx, rfl⟩
  obtain ⟨b, hb, m, q, he⟩ := (D.mem_sourceThickening_iff B Λ x).mp hx
  have hbO : (b : K) ∈ D.sourceSubring O Λ := by
    have hle : generatedOver B {y | ∃ n ∈ Λ, y = (D.ratio n : K)} ≤
        D.sourceSubring O Λ := by
      apply generatedOver_le
      · exact hBO.trans (D.coefficient_le_sourceSubring O Λ)
      · rintro y ⟨n, hn, rfl⟩
        exact ⟨D.ringRatio O n,
          base_le_idealThickening _ _ (D.selectedRatio_mem O Λ hn), rfl⟩
    exact hle (D.selectedBase_coe_mem B Λ b hb)
  have hqB : (D.endpoint m : K) * (q : K) ∈ D.sourceJunk B :=
    (D.mem_sourceJunk_iff_endpoint_mul B _).mpr ⟨m, q, rfl⟩
  have hqO := D.sourceJunk_le_sourceSubring O Λ (D.sourceJunk_mono hBO hqB)
  have he' := congrArg (D.sourceRing B).subtype he
  change (x : K) = (b : K) + (D.endpoint m : K) * (q : K) at he'
  change (x : K) ∈ D.sourceSubring O Λ
  rw [he']
  exact (D.sourceSubring O Λ).add_mem hbO hqO

/-- A selected polynomial over `B` that belongs to the larger endpoint ideal
already belongs to the literal endpoint ideal over `B`. -/
theorem selectedBase_mem_sourceJunk_shrunk_of_kernel
    (B O : Subring K) [IsDiscreteValuationRing O] (hBO : B ≤ O)
    (π : B) (hπirr : Irreducible (Subring.inclusion hBO π))
    (hπ : (π : K) = (D.uniformizer : K))
    (hO : ∀ a : O, D.valuation (a : K) ≤ 1)
    (hAF : UniformizerDivisionClosed B π D.valuation) (Λ : Set ℕ)
    (hkernel : ∀ n, 0 < n → ∀ f : Laurent (FractionRing O) n,
      f ∈ D.formalRing O (Subring.inclusion hBO π) n → D.evaluation O n f = 0 →
        f ∈ modelKernelJunk (coefficientFractionValuation O D.valuation)
          (algebraMap O (FractionRing O) (Subring.inclusion hBO π)) (D.modelParameters n))
    (b : D.sourceRing B) (hb : b ∈ D.selectedBase B Λ)
    (hbj : (b : K) ∈ D.sourceJunk O) : (b : K) ∈ D.sourceJunk B := by
  let πO := Subring.inclusion hBO π
  obtain ⟨m, q, he⟩ := (D.mem_sourceJunk_iff_endpoint_mul O (b : K)).mp hbj
  obtain ⟨Np, hNp⟩ := D.exists_shrunkSelectedFormal_lift_ge B O hBO Λ b hb
  obtain ⟨Nq, hNq⟩ := D.exists_formal_lift_ge O πO hπ q
  let n := max 1 (max m (max Np Nq))
  have hn : 0 < n := by dsimp [n]; omega
  have hm : m ≤ n := by dsimp [n]; omega
  obtain ⟨p, hp, hep⟩ := hNp n (by dsimp [n]; omega)
  obtain ⟨r, hr, her⟩ := hNq n (by dsimp [n]; omega)
  let z : Laurent (FractionRing O) n := endpointMonomial (algebraMap O (FractionRing O) πO) D.exponent m
  have hz : z ∈ D.formalRing O πO n :=
    Subring.subset_closure (FormalGenerator.endpoint m hm)
  have hzj : z * r ∈ modelJunk (coefficientFractionValuation O D.valuation)
      (algebraMap O (FractionRing O) πO) (D.modelParameters n) := by
    have hh := modelJunk_mul_left _ _ _ (D.formalRing_le_modelRing O πO hπ hO n hr)
      (endpointMonomial_mem_modelJunk _ _ (D.modelParameters n) m)
    simpa only [modelParameters, mul_comm] using hh
  have hzero : D.evaluation O n (p - z * r) = 0 := by
    rw [map_sub, map_mul, hep, her, D.evaluation_endpoint O πO hπ m hm]
    exact sub_eq_zero.mpr he
  have hformal : p - z * r ∈ D.formalRing O πO n :=
    (D.formalRing O πO n).sub_mem
      (D.shrunkSelectedFormalRing_le_formalRing B O hBO πO Λ n hp)
      ((D.formalRing O πO n).mul_mem hz hr)
  have hdiff := modelKernelJunk_le_modelJunk _ _ _ (hkernel n hn _ hformal hzero)
  have hpj : p ∈ modelJunk (coefficientFractionValuation O D.valuation)
      (algebraMap O (FractionRing O) πO) (D.modelParameters n) := by
    simpa only [sub_add_cancel] using (modelJunk _ _ _).add_mem hdiff hzj
  rw [← hep]
  exact D.exists_sourceIdeal_evaluation_of_mem_modelJunk_shrunk B O hBO π hπirr hπ hO hAF
    p (fun β _ => shrunkSelectedFormalRing_coeff B O hBO Λ hp β)
    (fun β hβ => (shrunkSelectedFormalRing_term B O hBO Λ hp β hβ).2.1) hpj

/-- The intersection formula for additive subgroups of the ambient field.
The kernel hypothesis is discharged by the arbitrary-block growth theorem below. -/
theorem sourceJunk_inter_sourceSubring_eq_shrunk_of_kernel
    (B O : Subring K) [IsDiscreteValuationRing O] (hBO : B ≤ O)
    (π : B) (hπirr : Irreducible (Subring.inclusion hBO π))
    (hπ : (π : K) = (D.uniformizer : K))
    (hO : ∀ a : O, D.valuation (a : K) ≤ 1)
    (hAF : UniformizerDivisionClosed B π D.valuation) (Λ : Set ℕ)
    (hkernel : ∀ n, 0 < n → ∀ f : Laurent (FractionRing O) n,
      f ∈ D.formalRing O (Subring.inclusion hBO π) n → D.evaluation O n f = 0 →
        f ∈ modelKernelJunk (coefficientFractionValuation O D.valuation)
          (algebraMap O (FractionRing O) (Subring.inclusion hBO π)) (D.modelParameters n)) :
    (D.sourceSubring B Λ).toAddSubgroup ⊓ D.sourceJunk O = D.sourceJunk B := by
  apply le_antisymm
  · rintro x ⟨hxS, hxJ⟩
    obtain ⟨x, hx, rfl⟩ := hxS
    obtain ⟨b, hb, m, q, he⟩ := (D.mem_sourceThickening_iff B Λ x).mp hx
    have hqB : (D.endpoint m : K) * (q : K) ∈ D.sourceJunk B :=
      (D.mem_sourceJunk_iff_endpoint_mul B _).mpr ⟨m, q, rfl⟩
    have hbO : (b : K) ∈ D.sourceJunk O := by
      have hh := (D.sourceJunk O).sub_mem hxJ (D.sourceJunk_mono hBO hqB)
      change (x : K) - (D.endpoint m : K) * (q : K) ∈ D.sourceJunk O at hh
      have he' := congrArg (D.sourceRing B).subtype he
      change (x : K) = (b : K) + (D.endpoint m : K) * (q : K) at he'
      simpa only [he', add_sub_cancel_right] using hh
    have hbB := D.selectedBase_mem_sourceJunk_shrunk_of_kernel B O hBO π hπirr hπ hO hAF
      Λ hkernel b hb hbO
    have he' := congrArg (D.sourceRing B).subtype he
    change (x : K) = (b : K) + (D.endpoint m : K) * (q : K) at he'
    change (x : K) ∈ D.sourceJunk B
    rw [he']
    exact (D.sourceJunk B).add_mem hbB hqB
  · exact le_inf (D.sourceJunk_le_sourceSubring B Λ) (D.sourceJunk_mono hBO)

/-- Shrinking the coefficient ring transfers the full outside-junk factorization exclusion to `B`.
Reflection follows from the equality of the endpoint ideals. -/
theorem noOutsideJunkFactorization_shrunk_of_kernel
    (B O : Subring K) [IsDiscreteValuationRing O] (hBO : B ≤ O)
    (π : B) (hπirr : Irreducible (Subring.inclusion hBO π))
    (hπ : (π : K) = (D.uniformizer : K))
    (hO : ∀ a : O, D.valuation (a : K) ≤ 1)
    (hAF : UniformizerDivisionClosed B π D.valuation)
    (Λ : Set ℕ) (hΛ : D.AdmissibleTail Λ)
    (hkernel : ∀ n, 0 < n → ∀ f : Laurent (FractionRing O) n,
      f ∈ D.formalRing O (Subring.inclusion hBO π) n → D.evaluation O n f = 0 →
        f ∈ modelKernelJunk (coefficientFractionValuation O D.valuation)
          (algebraMap O (FractionRing O) (Subring.inclusion hBO π)) (D.modelParameters n)) :
    D.NoOutsideJunkFactorization B Λ := by
  have hclaim := D.sourceJunk_inter_sourceSubring_eq_shrunk_of_kernel B O hBO π hπirr hπ hO
    hAF Λ hkernel
  have hno := D.noOutsideJunkFactorization_of_kernel O (Subring.inclusion hBO π) hπirr hπ hO
    Λ (hΛ.model_budget D) hkernel
  intro n f hf hnj
  apply hno n f (fun i => D.sourceSubring_mono hBO Λ (hf i))
  intro i hJ
  apply hnj i
  rw [← hclaim]
  exact ⟨hf i, hJ⟩

/-- A coefficient-transfer certificate for every admissible tail, with an intermediate kernel input. -/
theorem source_certificate_shrunk_of_kernel
    (B O : Subring K) [IsDiscreteValuationRing O] (hBO : B ≤ O)
    (π : B) (hπirr : Irreducible (Subring.inclusion hBO π))
    (hπ : (π : K) = (D.uniformizer : K))
    (hO : ∀ a : O, D.valuation (a : K) ≤ 1)
    (hAF : UniformizerDivisionClosed B π D.valuation)
    (Λ : Set ℕ) (hΛ : D.AdmissibleTail Λ)
    (hkernel : ∀ n, 0 < n → ∀ f : Laurent (FractionRing O) n,
      f ∈ D.formalRing O (Subring.inclusion hBO π) n → D.evaluation O n f = 0 →
        f ∈ modelKernelJunk (coefficientFractionValuation O D.valuation)
          (algebraMap O (FractionRing O) (Subring.inclusion hBO π)) (D.modelParameters n)) :
    D.NoOutsideJunkFactorization B Λ ∧
      ¬ Factorization.IsAtomicDomain (D.sourceSubring B Λ) := by
  have hno := D.noOutsideJunkFactorization_shrunk_of_kernel B O hBO π hπirr hπ hO hAF Λ hΛ hkernel
  exact ⟨hno, D.sourceSubring_not_atomic_of_no_factorization B
    (fun a => hO (Subring.inclusion hBO a)) Λ hΛ.cofinal hno⟩


/-- A nonatomic literal source subring contained in the original source
contradicts hereditary atomicity there; the inclusion is the actual field inclusion. -/
theorem source_not_hereditarilyAtomic_of_shrunk_certificate
    (B : Subring K) (hBR : B ≤ R) (Λ : Set ℕ)
    (hnot : ¬ Factorization.IsAtomicDomain (D.sourceSubring B Λ)) :
    ¬ Factorization.IsHereditarilyAtomic R := by
  intro hR
  exact hnot (hR.of_injective (Subring.inclusion (D.sourceSubring_le B hBR Λ))
    (Subring.inclusion_injective (D.sourceSubring_le B hBR Λ))).isAtomicDomain

/-- All source-side coefficient-transfer conclusions for a specified coefficient ring and tail.
The endpoint ideal is literally `sourceIdeal B`, an ideal of `sourceRing B`. -/
structure ShrunkSourceCertificate (B : Subring K) (Λ : Set ℕ) : Prop where
  ring_le_source : D.sourceRing B ≤ R
  ring_bounded : ∀ x : D.sourceRing B, D.valuation (x : K) ≤ 1
  endpoint_mem_junk : (D.endpoint 1 : K) ∈ D.sourceJunk B
  endpoint_nonzero : (D.endpoint 1 : K) ≠ 0
  endpoint_nonunit : ¬ IsUnit
    (⟨D.endpoint 1, D.endpoint_mem_sourceSubring B Λ 1⟩ : D.sourceSubring B Λ)
  no_junk_atoms : ∀ x : D.sourceSubring B Λ,
    (x : K) ∈ D.sourceJunk B → ¬ Irreducible x
  no_outside_junk_factorization : D.NoOutsideJunkFactorization B Λ
  not_atomic : ¬ Factorization.IsAtomicDomain (D.sourceSubring B Λ)
  source_not_hereditarilyAtomic : ¬ Factorization.IsHereditarilyAtomic R

/-- Generic algebra and positive valuation complete the source-side certificate
once the exact factorization obstruction has been proved. -/
theorem shrunkSourceCertificate_of_noOutsideJunkFactorization
    (B : Subring K) (hBR : B ≤ R)
    (hB : ∀ a : B, D.valuation (a : K) ≤ 1)
    (Λ : Set ℕ) (hcofinal : ∀ N : ℕ, ∃ m, N ≤ m ∧ m ∈ Λ)
    (hno : D.NoOutsideJunkFactorization B Λ) : D.ShrunkSourceCertificate B Λ := by
  have hnot := D.sourceSubring_not_atomic_of_no_factorization B hB Λ hcofinal hno
  refine ⟨D.sourceRing_le B hBR, D.sourceRing_bounded B hB,
    D.endpoint_mem_sourceJunk B 1, Subtype.coe_ne_coe.mpr (D.endpoint_ne_zero 1), ?_,
    ?_, hno, hnot, D.source_not_hereditarilyAtomic_of_shrunk_certificate B hBR Λ hnot⟩
  · exact not_isUnit_of_mapped_order_pos (D.sourceSubring B Λ).subtype D.valuation
      (D.sourceSubring_bounded B hB Λ)
      (lt_of_lt_of_le zero_lt_one (D.endpoint_order_ge_one 1))
  · intro x hx hirr
    exact D.sourceSubring_irreducible_not_mem_junk B hB Λ hcofinal x hirr hx

/-- The intersection formula for arbitrary supplied blocks satisfying the degree-growth inequality. Kernel inclusion is
proved from the displayed growth and compatible completion data. The selection
need not be cofinal and has no weight-budget restriction for this equality. -/
theorem sourceJunk_inter_sourceSubring_eq_shrunk_of_growth
    {k E : Type*} [NontriviallyNormedField k] [CompleteSpace k]
    [NormedField E] [NormedAlgebra k E] [IsUltrametricDist E]
    (y : ℕ → Eˣ) (hy : ∀ j, IsAlgebraic k (y j : E))
    (C : ℕ → ℝ) (hC : ∀ j, 1 ≤ C j)
    (hb : ∀ j (z : movingField k y j) i,
      ‖(movingTowerBasis k y hy j).repr z i • movingTowerBasis k y hy j i‖ ≤ C j * ‖z‖)
    (hgrowth : ∀ j, 3 * (D.exponent : ℝ) * (2 * D.threshold (j + 1) + Real.log (C j)) ≤
      (movingDegree k y j : ℝ) * D.weight j)
    (B O : Subring K) [IsDiscreteValuationRing O] (hBO : B ≤ O)
    (π : B) (hπirr : Irreducible (Subring.inclusion hBO π))
    (hπ : (π : K) = (D.uniformizer : K))
    (hO : ∀ a : O, D.valuation (a : K) ≤ 1)
    (hAF : UniformizerDivisionClosed B π D.valuation)
    (v : Valuation k ℝ≥0) (hv : ∀ a : k, realValuationOrder v a = -Real.log ‖a‖)
    (f : FractionRing O →+* k)
    (hf : ∀ a, v (f a) = coefficientFractionValuation O D.valuation a)
    (g : K →+* E) (hgy : ∀ j, (y j : E) = g (D.ratio j : K))
    (hgw : ∀ j, realValuationOrder D.valuation (D.ratio j : K) =
      -Real.log ‖g (D.ratio j : K)‖)
    (hcoeff : (algebraMap k E).comp f = g.comp (coefficientFractionEmbedding O))
    (Λ : Set ℕ) :
    (D.sourceSubring B Λ).toAddSubgroup ⊓ D.sourceJunk O = D.sourceJunk B :=
  D.sourceJunk_inter_sourceSubring_eq_shrunk_of_kernel B O hBO π hπirr hπ hO hAF Λ
    (D.source_kernel_mem_of_growth y hy C hC hb hgrowth O
      (Subring.inclusion hBO π) hπ hO v hv f hf g hgy hgw hcoeff)

/-- Coefficient transfer transfer over a division-closed coefficient subring for every
admissible tail of arbitrary growth-controlled blocks. No kernel or non-junk
reflection conclusion is assumed. -/
theorem source_certificate_shrunk_of_growth
    {k E : Type*} [NontriviallyNormedField k] [CompleteSpace k]
    [NormedField E] [NormedAlgebra k E] [IsUltrametricDist E]
    (y : ℕ → Eˣ) (hy : ∀ j, IsAlgebraic k (y j : E))
    (C : ℕ → ℝ) (hC : ∀ j, 1 ≤ C j)
    (hb : ∀ j (z : movingField k y j) i,
      ‖(movingTowerBasis k y hy j).repr z i • movingTowerBasis k y hy j i‖ ≤ C j * ‖z‖)
    (hgrowth : ∀ j, 3 * (D.exponent : ℝ) * (2 * D.threshold (j + 1) + Real.log (C j)) ≤
      (movingDegree k y j : ℝ) * D.weight j)
    (B O : Subring K) [IsDiscreteValuationRing O] (hBO : B ≤ O)
    (π : B) (hπirr : Irreducible (Subring.inclusion hBO π))
    (hπ : (π : K) = (D.uniformizer : K))
    (hO : ∀ a : O, D.valuation (a : K) ≤ 1)
    (hAF : UniformizerDivisionClosed B π D.valuation)
    (v : Valuation k ℝ≥0) (hv : ∀ a : k, realValuationOrder v a = -Real.log ‖a‖)
    (f : FractionRing O →+* k)
    (hf : ∀ a, v (f a) = coefficientFractionValuation O D.valuation a)
    (g : K →+* E) (hgy : ∀ j, (y j : E) = g (D.ratio j : K))
    (hgw : ∀ j, realValuationOrder D.valuation (D.ratio j : K) =
      -Real.log ‖g (D.ratio j : K)‖)
    (hcoeff : (algebraMap k E).comp f = g.comp (coefficientFractionEmbedding O))
    (Λ : Set ℕ) (hΛ : D.AdmissibleTail Λ) :
    D.NoOutsideJunkFactorization B Λ ∧
      ¬ Factorization.IsAtomicDomain (D.sourceSubring B Λ) :=
  D.source_certificate_shrunk_of_kernel B O hBO π hπirr hπ hO hAF Λ hΛ
    (D.source_kernel_mem_of_growth y hy C hC hb hgrowth O
      (Subring.inclusion hBO π) hπ hO v hv f hf g hgy hgw hcoeff)

/-- Coefficient transfer also supplies an actual terminal tail, retaining the literal source
ring over `B` and its endpoint ideal. -/
theorem exists_source_certificate_shrunk_of_growth
    {k E : Type*} [NontriviallyNormedField k] [CompleteSpace k]
    [NormedField E] [NormedAlgebra k E] [IsUltrametricDist E]
    (y : ℕ → Eˣ) (hy : ∀ j, IsAlgebraic k (y j : E))
    (C : ℕ → ℝ) (hC : ∀ j, 1 ≤ C j)
    (hb : ∀ j (z : movingField k y j) i,
      ‖(movingTowerBasis k y hy j).repr z i • movingTowerBasis k y hy j i‖ ≤ C j * ‖z‖)
    (hgrowth : ∀ j, 3 * (D.exponent : ℝ) * (2 * D.threshold (j + 1) + Real.log (C j)) ≤
      (movingDegree k y j : ℝ) * D.weight j)
    (B O : Subring K) [IsDiscreteValuationRing O] (hBO : B ≤ O)
    (π : B) (hπirr : Irreducible (Subring.inclusion hBO π))
    (hπ : (π : K) = (D.uniformizer : K))
    (hO : ∀ a : O, D.valuation (a : K) ≤ 1)
    (hAF : UniformizerDivisionClosed B π D.valuation)
    (v : Valuation k ℝ≥0) (hv : ∀ a : k, realValuationOrder v a = -Real.log ‖a‖)
    (f : FractionRing O →+* k)
    (hf : ∀ a, v (f a) = coefficientFractionValuation O D.valuation a)
    (g : K →+* E) (hgy : ∀ j, (y j : E) = g (D.ratio j : K))
    (hgw : ∀ j, realValuationOrder D.valuation (D.ratio j : K) =
      -Real.log ‖g (D.ratio j : K)‖)
    (hcoeff : (algebraMap k E).comp f = g.comp (coefficientFractionEmbedding O)) :
    ∃ Λ : Set ℕ, (∃ N : ℕ, 1 ≤ N ∧ Λ = Set.Ici N) ∧
      0 ∉ Λ ∧ (∀ m : ℕ, ∃ l, m ≤ l ∧ l ∈ Λ) ∧
      D.NoOutsideJunkFactorization B Λ ∧
      ¬ Factorization.IsAtomicDomain (D.sourceSubring B Λ) := by
  obtain ⟨N, hN, hΛ⟩ := D.exists_admissibleTail
  obtain ⟨hno, hnonatomic⟩ := D.source_certificate_shrunk_of_growth y hy C hC hb hgrowth
    B O hBO π hπirr hπ hO hAF v hv f hf g hgy hgw hcoeff (Set.Ici N) hΛ
  exact ⟨Set.Ici N, ⟨N, hN, rfl⟩, zero_not_mem_tail_indices hN, hΛ.cofinal, hno, hnonatomic⟩

/-- Coefficient transfer, including containment, atomless junk, the nonzero nonunit
endpoint, atomless splitting, nonatomicity, and failure of HA for the original source. The
coefficient DVR need not lie in that source; only `B ≤ R` is required. -/
theorem abu_certificate_of_growth
    {k E : Type*} [NontriviallyNormedField k] [CompleteSpace k]
    [NormedField E] [NormedAlgebra k E] [IsUltrametricDist E]
    (y : ℕ → Eˣ) (hy : ∀ j, IsAlgebraic k (y j : E))
    (C : ℕ → ℝ) (hC : ∀ j, 1 ≤ C j)
    (hb : ∀ j (z : movingField k y j) i,
      ‖(movingTowerBasis k y hy j).repr z i • movingTowerBasis k y hy j i‖ ≤ C j * ‖z‖)
    (hgrowth : ∀ j, 3 * (D.exponent : ℝ) * (2 * D.threshold (j + 1) + Real.log (C j)) ≤
      (movingDegree k y j : ℝ) * D.weight j)
    (B O : Subring K) [IsDiscreteValuationRing O] (hBO : B ≤ O)
    (π : B) (hπirr : Irreducible (Subring.inclusion hBO π))
    (hπ : (π : K) = (D.uniformizer : K))
    (hO : ∀ a : O, D.valuation (a : K) ≤ 1)
    (hAF : UniformizerDivisionClosed B π D.valuation)
    (v : Valuation k ℝ≥0) (hv : ∀ a : k, realValuationOrder v a = -Real.log ‖a‖)
    (f : FractionRing O →+* k)
    (hf : ∀ a, v (f a) = coefficientFractionValuation O D.valuation a)
    (g : K →+* E) (hgy : ∀ j, (y j : E) = g (D.ratio j : K))
    (hgw : ∀ j, realValuationOrder D.valuation (D.ratio j : K) =
      -Real.log ‖g (D.ratio j : K)‖)
    (hcoeff : (algebraMap k E).comp f = g.comp (coefficientFractionEmbedding O))
    (hBR : B ≤ R) (Λ : Set ℕ) (hΛ : D.AdmissibleTail Λ) :
    D.ShrunkSourceCertificate B Λ := by
  have hno := (D.source_certificate_shrunk_of_growth y hy C hC hb hgrowth
    B O hBO π hπirr hπ hO hAF v hv f hf g hgy hgw hcoeff Λ hΛ).1
  exact D.shrunkSourceCertificate_of_noOutsideJunkFactorization B hBR
    (fun a => hO (Subring.inclusion hBO a)) Λ hΛ.cofinal hno

end SourceBlockData
end HereditaryAtomicity.DVRBase
