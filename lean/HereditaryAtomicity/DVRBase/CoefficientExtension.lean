import HereditaryAtomicity.DVRBase.SourceLaurent
import HereditaryAtomicity.DVRBase.ModelSource
import HereditaryAtomicity.DVRBase.ValuationNorm

/-!
# Literal coefficient extension and commuting evaluation

The Laurent exponent vectors stay fixed. Coefficients are mapped through an
explicit field homomorphism, and valuations agree exactly where required.
No discreteness of the ambient field is assumed.
-/

noncomputable section
namespace HereditaryAtomicity.DVRBase
open scoped NNReal BigOperators

variable {k l K L : Type*} [Field k] [Field l] [Field K] [Field L] {n : ℕ}

/-- The actual coefficient map of finite Laurent algebras. -/
def laurentMap (f : k →+* l) (n : ℕ) : Laurent k n →+* Laurent l n :=
  AddMonoidAlgebra.mapRingHom (Fin n → ℤ) f

@[simp] theorem laurentMap_coeff (f : k →+* l) (p : Laurent k n) (β : Fin n → ℤ) :
    (laurentMap f n p).coeff β = f (p.coeff β) :=
  AddMonoidAlgebra.coeff_mapRingHom _ _ _

@[simp] theorem laurentMap_single (f : k →+* l) (β : Fin n → ℤ) (c : k) :
    laurentMap f n (AddMonoidAlgebra.single β c) = AddMonoidAlgebra.single β (f c) :=
  AddMonoidAlgebra.mapRingHom_single _ _ _

@[simp] theorem laurentMap_variable (f : k →+* l) (i : Fin n) :
    laurentMap f n (variableMonomial i) = variableMonomial i := by
  simp [variableMonomial]

@[simp] theorem laurentMap_terminal (f : k →+* l) (π : k) (κ : ℕ) :
    laurentMap f n (terminalMonomial π κ) = terminalMonomial (f π) κ := by
  simp [terminalMonomial]

@[simp] theorem laurentMap_endpoint (f : k →+* l) (π : k) (κ j : ℕ) :
    laurentMap f n (endpointMonomial π κ j) = endpointMonomial (f π) κ j := by
  simp [endpointMonomial]

theorem laurentMap_injective (f : k →+* l) : Function.Injective (laurentMap f n) := by
  intro p q h
  ext β
  exact f.injective (by simpa using congrArg (fun a : Laurent l n => a.coeff β) h)

/-- Exact valuation agreement preserves every literal coefficient order. -/
theorem realValuationOrder_map (f : k →+* l) (v : Valuation k ℝ≥0)
    (w : Valuation l ℝ≥0) (hv : ∀ c, w (f c) = v c) (c : k) :
    realValuationOrder w (f c) = realValuationOrder v c := by
  simp only [realValuationOrder, hv]

theorem termOrder_map (f : k →+* l) (v : Valuation k ℝ≥0)
    (w : Valuation l ℝ≥0) (hv : ∀ c, w (f c) = v c)
    (u : Fin n → ℝ) (β : Fin n → ℤ) (c : k) :
    termOrder w u β (f c) = termOrder v u β c := by
  rw [termOrder, termOrder, realValuationOrder_map f v w hv]

/-- Any coefficient-order support condition is preserved and reflected by
this explicit coefficient embedding. -/
theorem laurentMap_mem_supported_iff (f : k →+* l) (v : Valuation k ℝ≥0)
    (w : Valuation l ℝ≥0) (hv : ∀ c, w (f c) = v c)
    (M : MonomialClass n) (p : Laurent k n) :
    laurentMap f n p ∈ M.supported w ↔ p ∈ M.supported v := by
  simp only [MonomialClass.mem_supported, laurentMap_coeff,
    map_ne_zero_iff f f.injective, realValuationOrder_map f v w hv]

/-- Actual model-generator membership is preserved by coefficient extension. -/
theorem laurentMap_mem_modelRing (f : k →+* l) (v : Valuation k ℝ≥0)
    (w : Valuation l ℝ≥0) (hv : ∀ c, w (f c) = v c) (π : k) (P : ModelParameters n)
    {p : Laurent k n} (hp : p ∈ modelRing v π P) :
    laurentMap f n p ∈ modelRing w (f π) P := by
  have hle : modelRing v π P ≤ (modelRing w (f π) P).comap (laurentMap f n) := by
    apply Subring.closure_le.mpr
    intro p hp
    change laurentMap f n p ∈ modelRing w (f π) P
    cases hp with
    | constant c hc =>
        rw [laurentMap_single]
        exact modelRing_constant w (f π) P (f c) (by simpa only [hv] using hc)
    | coordinate i => simpa using modelRing_variable w (f π) P i
    | terminal => simpa using modelRing_terminal w (f π) P
    | high j hj0 hjn β c hc hs ht =>
        rw [laurentMap_single]
        exact modelRing_high w (f π) P j hj0 hjn β (f c)
          ((map_ne_zero_iff f f.injective).mpr hc) hs (by rwa [termOrder_map f v w hv])
  exact hle hp

theorem laurentMap_mem_modelJunk (f : k →+* l) (v : Valuation k ℝ≥0)
    (w : Valuation l ℝ≥0) (hv : ∀ c, w (f c) = v c) (π : k) (P : ModelParameters n)
    {p : Laurent k n} (hp : p ∈ modelJunk v π P) :
    laurentMap f n p ∈ modelJunk w (f π) P := by
  obtain ⟨q, hq, rfl⟩ := hp
  exact ⟨laurentMap f n q, laurentMap_mem_modelRing f v w hv π P hq, by simp⟩

theorem laurentMap_mem_modelPolynomialRing (f : k →+* l) (v : Valuation k ℝ≥0)
    (w : Valuation l ℝ≥0) (hv : ∀ c, w (f c) = v c) (Λ : Finset (Fin n))
    {p : Laurent k n} (hp : p ∈ modelPolynomialRing v Λ) :
    laurentMap f n p ∈ modelPolynomialRing w Λ := by
  have hle : modelPolynomialRing v Λ ≤ (modelPolynomialRing w Λ).comap (laurentMap f n) := by
    apply Subring.closure_le.mpr
    intro p hp
    change laurentMap f n p ∈ modelPolynomialRing w Λ
    cases hp with
    | constant c hc =>
        rw [laurentMap_single]
        exact modelPolynomialRing_constant w Λ (f c) (by simpa only [hv] using hc)
    | coordinate i hi => simpa using modelPolynomialRing_variable w Λ i hi
  exact hle hp

theorem laurentMap_mem_modelSourceRing (f : k →+* l) (v : Valuation k ℝ≥0)
    (w : Valuation l ℝ≥0) (hv : ∀ c, w (f c) = v c) (π : k)
    (P : ModelParameters n) (Λ : Finset (Fin n))
    {p : Laurent k n} (hp : p ∈ modelSourceRing v π P Λ) :
    laurentMap f n p ∈ modelSourceRing w (f π) P Λ := by
  obtain ⟨a, ha, j, hj, rfl⟩ := (mem_modelSourceRing v π P Λ p).mp hp
  exact (mem_modelSourceRing w (f π) P Λ _).mpr
    ⟨laurentMap f n a, laurentMap_mem_modelPolynomialRing f v w hv Λ ha,
      laurentMap f n j, laurentMap_mem_modelJunk f v w hv π P hj, by simp⟩

/-- Exact valuation agreement also reflects actual model-ring membership. -/
theorem laurentMap_mem_modelRing_iff (f : k →+* l) (v : Valuation k ℝ≥0)
    (w : Valuation l ℝ≥0) (hv : ∀ c, w (f c) = v c)
    (π : k) (hπ0 : π ≠ 0) (hπ : realValuationOrder v π = 1)
    (P : ModelParameters n) (p : Laurent k n) :
    laurentMap f n p ∈ modelRing w (f π) P ↔ p ∈ modelRing v π P := by
  have hfπ : realValuationOrder w (f π) = 1 := (realValuationOrder_map f v w hv π).trans hπ
  rw [modelRing_eq_supported w (f π) ((map_ne_zero_iff f f.injective).mpr hπ0) hfπ P,
    modelRing_eq_supported v π hπ0 hπ P]
  exact laurentMap_mem_supported_iff f v w hv P.ringClass p

theorem laurentMap_mem_modelJunk_iff (f : k →+* l) (v : Valuation k ℝ≥0)
    (w : Valuation l ℝ≥0) (hv : ∀ c, w (f c) = v c)
    (π : k) (hπ0 : π ≠ 0) (hπ : realValuationOrder v π = 1)
    (P : ModelParameters n) (p : Laurent k n) :
    laurentMap f n p ∈ modelJunk w (f π) P ↔ p ∈ modelJunk v π P := by
  have hfπ : realValuationOrder w (f π) = 1 := (realValuationOrder_map f v w hv π).trans hπ
  rw [modelJunk_eq_supported w (f π) ((map_ne_zero_iff f f.injective).mpr hπ0) hfπ P,
    modelJunk_eq_supported v π hπ0 hπ P]
  exact laurentMap_mem_supported_iff f v w hv _ p

theorem laurentMap_mem_modelPolynomialRing_iff (f : k →+* l) (v : Valuation k ℝ≥0)
    (w : Valuation l ℝ≥0) (hv : ∀ c, w (f c) = v c)
    (Λ : Finset (Fin n)) (p : Laurent k n) :
    laurentMap f n p ∈ modelPolynomialRing w Λ ↔ p ∈ modelPolynomialRing v Λ := by
  rw [modelPolynomialRing_eq_supported, modelPolynomialRing_eq_supported]
  exact laurentMap_mem_supported_iff f v w hv _ p

theorem laurentMap_mem_modelSourceRing_iff (f : k →+* l) (v : Valuation k ℝ≥0)
    (w : Valuation l ℝ≥0) (hv : ∀ c, w (f c) = v c)
    (π : k) (hπ0 : π ≠ 0) (hπ : realValuationOrder v π = 1)
    (P : ModelParameters n) (Λ : Finset (Fin n)) (p : Laurent k n) :
    laurentMap f n p ∈ modelSourceRing w (f π) P Λ ↔ p ∈ modelSourceRing v π P Λ := by
  have hfπ : realValuationOrder w (f π) = 1 := (realValuationOrder_map f v w hv π).trans hπ
  change laurentMap f n p ∈ (modelSourceRing w (f π) P Λ).toAddSubgroup ↔
    p ∈ (modelSourceRing v π P Λ).toAddSubgroup
  rw [modelSourceRing_eq_supported w (f π) ((map_ne_zero_iff f f.injective).mpr hπ0) hfπ P Λ,
    modelSourceRing_eq_supported v π hπ0 hπ P Λ]
  exact laurentMap_mem_supported_iff f v w hv _ p

/-- Coefficient extension commutes with actual evaluation whenever the field
maps commute and the target ratios are the mapped source ratios. -/
theorem laurentEvaluation_map (f : k →+* l) (g : K →+* L)
    (a : k →+* K) (b : l →+* L) (hsquare : b.comp f = g.comp a)
    (y : Fin n → K) (hy : ∀ i, y i ≠ 0) (p : Laurent k n) :
    laurentEvaluation b (fun i => g (y i))
        (fun i => (map_ne_zero_iff g g.injective).mpr (hy i)) (laurentMap f n p) =
      g (laurentEvaluation a y hy p) := by
  rw [← AddMonoidAlgebra.sum_coeff_single p, Finsupp.sum]
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro β _
  have hs := DFunLike.congr_fun hsquare (p.coeff β)
  simp only [RingHom.comp_apply] at hs
  simp [hs, map_zpow₀]

/-- The canonical extension of a valuation-preserving field map to the two
literal valuation completions. -/
def completionExtension (f : k →+* K) (v : Valuation k ℝ≥0) (w : Valuation K ℝ≥0)
    (hv : ∀ c, w (f c) = v c) :
    ValuationNormCompletion v →+* ValuationNormCompletion w := by
  let : Algebra k K := f.toAlgebra
  let := valuationCompletionNormedAlgebra v w hv
  exact algebraMap (ValuationNormCompletion v) (ValuationNormCompletion w)

/-- The extended coefficient map completes the original commuting square. -/
theorem completionExtension_algebraMap (f : k →+* K)
    (v : Valuation k ℝ≥0) (w : Valuation K ℝ≥0)
    (hv : ∀ c, w (f c) = v c) (x : k) :
    completionExtension f v w hv (algebraMap k (ValuationNormCompletion v) x) =
      algebraMap K (ValuationNormCompletion w) (f x) := by
  let : Algebra k K := f.toAlgebra
  let := valuationCompletionNormedAlgebra v w hv
  let := valuationCompletion_scalarTower v w hv
  change algebraMap (ValuationNormCompletion v) (ValuationNormCompletion w)
    (algebraMap k (ValuationNormCompletion v) x) = _
  rw [← IsScalarTower.algebraMap_apply k (ValuationNormCompletion v) (ValuationNormCompletion w),
    IsScalarTower.algebraMap_apply k K (ValuationNormCompletion w)]
  rfl

theorem completionExtension_valuation (f : k →+* K)
    (v : Valuation k ℝ≥0) (w : Valuation K ℝ≥0)
    (hv : ∀ c, w (f c) = v c) (x : ValuationNormCompletion v) :
    completionValuation w (completionExtension f v w hv x) = completionValuation v x := by
  let : Algebra k K := f.toAlgebra
  exact completionValuation_restrict v w hv x

/-- The concrete completion embedding of the original coefficient fraction field. -/
def coefficientCompletionEmbedding (O : Subring K) (v : Valuation K ℝ≥0) :
    ValuationNormCompletion (coefficientFractionValuation O v) →+* ValuationNormCompletion v :=
  completionExtension (coefficientFractionEmbedding O) (coefficientFractionValuation O v) v
    (fun _ => rfl)

@[simp] theorem coefficientCompletionEmbedding_algebraMap (O : Subring K)
    (v : Valuation K ℝ≥0) (x : FractionRing O) :
    coefficientCompletionEmbedding O v
        (algebraMap (FractionRing O) (ValuationNormCompletion (coefficientFractionValuation O v)) x) =
      algebraMap K (ValuationNormCompletion v) (coefficientFractionEmbedding O x) :=
  completionExtension_algebraMap _ _ _ _ x

@[simp] theorem coefficientCompletionEmbedding_valuation (O : Subring K)
    (v : Valuation K ℝ≥0) (x : ValuationNormCompletion (coefficientFractionValuation O v)) :
    completionValuation v (coefficientCompletionEmbedding O v x) =
      completionValuation (coefficientFractionValuation O v) x :=
  completionExtension_valuation _ _ _ _ x

namespace SourceBlockData
variable {R : Subring K} (D : SourceBlockData R)

/-- Evaluation with completed coefficient field and the completed images of
the original source ratios. -/
def completedEvaluation (O : Subring K) (n : ℕ) :
    Laurent (ValuationNormCompletion (coefficientFractionValuation O D.valuation)) n →+*
      ValuationNormCompletion D.valuation :=
  laurentEvaluation (coefficientCompletionEmbedding O D.valuation)
    (fun i => algebraMap K (ValuationNormCompletion D.valuation) (D.ratio i.val : K))
    (fun i => (map_ne_zero_iff _ (algebraMap K (ValuationNormCompletion D.valuation)).injective).mpr
      (Subtype.coe_ne_coe.mpr (D.ratio_ne_zero i.val)))

/-- Completing coefficients and then evaluating gives exactly the completed
image of the original evaluation. -/
theorem completedEvaluation_map (O : Subring K) (p : Laurent (FractionRing O) n) :
    D.completedEvaluation O n
        (laurentMap (algebraMap (FractionRing O)
          (ValuationNormCompletion (coefficientFractionValuation O D.valuation))) n p) =
      algebraMap K (ValuationNormCompletion D.valuation) (D.evaluation O n p) := by
  apply laurentEvaluation_map
  ext x
  exact coefficientCompletionEmbedding_algebraMap O D.valuation x

/-- The original and completed evaluations have exactly the same kernel. -/
theorem completedEvaluation_map_eq_zero_iff (O : Subring K) (p : Laurent (FractionRing O) n) :
    D.completedEvaluation O n
        (laurentMap (algebraMap (FractionRing O)
          (ValuationNormCompletion (coefficientFractionValuation O D.valuation))) n p) = 0 ↔
      D.evaluation O n p = 0 := by
  rw [D.completedEvaluation_map O p]
  exact map_eq_zero_iff _ (algebraMap K (ValuationNormCompletion D.valuation)).injective

end SourceBlockData
end HereditaryAtomicity.DVRBase
