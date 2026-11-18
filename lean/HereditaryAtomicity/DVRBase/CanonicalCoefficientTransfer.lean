import HereditaryAtomicity.DVRBase.CoefficientTransfer
import HereditaryAtomicity.DVRBase.LocalCertificate

/-!
# Completed coefficient-transfer construction from the original source chain

The coefficient DVR controls the model and completion, while only the shrunk
coefficient ring lies in the source. The selected endpoints and consecutive
ratio blocks remain literal elements of the original source ring throughout.
-/

noncomputable section
namespace HereditaryAtomicity.DVRBase
open scoped NNReal
variable {K : Type*} [Field K]

/-- Coefficient transfer from a supplied normalized source chain. The construction builds
its completion fields, moving-basis bounds and blocks internally. Only the
shrunk coefficient ring `B`, not the model DVR `O`, must lie in the source.
Every admissible tail has the original-DVR obstruction, the endpoint ideal intersection formula,
and all source-side coefficient-transfer conclusions over `B`. -/
theorem UniformizerChainData.exists_completed_shrunk_source_certificate
    (B O R : Subring K) [IsDiscreteValuationRing O] [Algebra.IsAlgebraic O K]
    (hBO : B ≤ O) (hBR : B ≤ R) (π : B)
    (hπ : Irreducible (Subring.inclusion hBO π)) {t : ℕ → R}
    (C : UniformizerChainData (Subring.inclusion hBR π) t)
    (w : Valuation K ℝ≥0) (hO : ∀ a : O, w (a : K) ≤ 1)
    (hnorm : realValuationOrder w (π : K) = 1)
    (hAF : UniformizerDivisionClosed B π w)
    (ht : ∀ n, 0 < realValuationOrder w (t n : K))
    (hc : ∀ n, 1 ≤ realValuationOrder w (C.endpoint n : K)) :
    ∃ (D : SourceBlockData R) (a l : ℕ → ℕ),
      D.uniformizer = Subring.inclusion hBR π ∧ D.exponent = C.exponent ∧
      D.valuation = w ∧ StrictMono a ∧ a 0 = 0 ∧
      (∀ n, a (n + 1) = a n + l n + 1) ∧
      (∀ n, D.endpoint n = C.endpoint (a n)) ∧
      (∀ n, D.ratio n = sourceBlock t (a n) (l n)) ∧
      ∀ Λ : Set ℕ, D.AdmissibleTail Λ →
        D.NoOutsideJunkFactorization O Λ ∧
        (D.sourceSubring B Λ).toAddSubgroup ⊓ D.sourceJunk O = D.sourceJunk B ∧
        D.ShrunkSourceCertificate B Λ := by
  let πO := Subring.inclusion hBO π
  let πR := Subring.inclusion hBR π
  let : Algebra (FractionRing O) K := (coefficientFractionEmbedding O).toAlgebra
  have halg (x : K) : IsAlgebraic (FractionRing O) x := by
    let : IsScalarTower O (FractionRing O) K :=
      IsScalarTower.of_algebraMap_eq fun z =>
        (coefficientFractionEmbedding_algebraMap O z).symm
    exact (Algebra.IsAlgebraic.isAlgebraic (R := O) x).extendScalars
      (IsFractionRing.injective O (FractionRing O))
  let I : BlockInput R (FractionRing O) K πR t := {
    chain := C
    embedding := R.subtype
    embedding_injective := Subtype.val_injective
    valuation := w
    coefficient_orders := fun z hz => coefficientFraction_order_integral O w hO hπ hnorm hz
    source_algebraic := fun r => halg (r : K)
    endpoint_order_ge_one := hc
    uniformizer_order := hnorm
    ratio_positive := ht }
  let v := coefficientFractionValuation O w
  have hπf0 : algebraMap O (FractionRing O) πO ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective O (FractionRing O))).mpr hπ.ne_zero
  have hπford : realValuationOrder v (algebraMap O (FractionRing O) πO) = 1 := by
    change realValuationOrder w
      (coefficientFractionEmbedding O (algebraMap O (FractionRing O) πO)) = 1
    rw [coefficientFractionEmbedding_algebraMap]
    exact hnorm
  have hπfv : v (algebraMap O (FractionRing O) πO) < 1 :=
    (realValuationOrder_pos_iff v hπf0).mp (by rw [hπford]; norm_num)
  let := valuationNormCompletion_nontriviallyNormedField v hπf0 hπfv
  let := valuationCompletionNormedAlgebra v w (fun _ => rfl)
  let J := I.completed v (fun _ => rfl)
  have hJw (r : R) : J.valuation (J.embedding r) = w (r : K) :=
    completionValuation_algebraMap w (r : K)
  let D := J.toSourceBlockData BlockState.basisLoss w hJw
  have hsquare : (algebraMap (ValuationNormCompletion v) (ValuationNormCompletion w)).comp
      (algebraMap (FractionRing O) (ValuationNormCompletion v)) =
    (algebraMap K (ValuationNormCompletion w)).comp (coefficientFractionEmbedding O) := by
    ext z
    exact coefficientCompletionEmbedding_algebraMap O w z
  refine ⟨D, J.index BlockState.basisLoss, J.length BlockState.basisLoss,
    rfl, rfl, rfl, J.index_strictMono _, J.index_zero _, J.index_succ _,
    (fun _ => rfl), (fun _ => rfl), ?_⟩
  intro Λ hΛ
  have hk : ∀ n, 0 < n → ∀ p : Laurent (FractionRing O) n,
      p ∈ D.formalRing O πO n → D.evaluation O n p = 0 →
        p ∈ modelKernelJunk (coefficientFractionValuation O w)
          (algebraMap O (FractionRing O) πO) (D.modelParameters n) := by
    intro n _ p hp hz
    exact J.source_kernel_mem w hJw (fun _ => rfl) O πO rfl hO
      (completionValuation v) (fun _ => rfl)
      (algebraMap (FractionRing O) (ValuationNormCompletion v))
      (completionValuation_algebraMap v)
      (algebraMap K (ValuationNormCompletion w)) (fun _ => rfl) hsquare p hp hz
  have hnoO := (D.source_certificate_of_kernel O πO hπ rfl hO Λ hΛ hk).1
  have hclaim := D.sourceJunk_inter_sourceSubring_eq_shrunk_of_kernel B O hBO π hπ rfl hO hAF Λ hk
  have hnoB := (D.source_certificate_shrunk_of_kernel B O hBO π hπ rfl hO hAF Λ hΛ hk).1
  exact ⟨hnoO, hclaim, D.shrunkSourceCertificate_of_noOutsideJunkFactorization B hBR
    (fun a => hO (Subring.inclusion hBO a)) Λ hΛ.cofinal hnoB⟩

end HereditaryAtomicity.DVRBase
