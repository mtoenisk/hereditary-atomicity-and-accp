import HereditaryAtomicity.DVRBase.BlockConstruction
import HereditaryAtomicity.DVRBase.ModelOrders
import HereditaryAtomicity.DVRBase.MovingLift
import HereditaryAtomicity.DVRBase.MovingMonomialOrder
import HereditaryAtomicity.DVRBase.SourceBlockAdapter
import HereditaryAtomicity.DVRBase.SourceModel
import HereditaryAtomicity.DVRBase.KernelIdeal
import HereditaryAtomicity.DVRBase.SourceProductNumerics
import HereditaryAtomicity.DVRBase.CoefficientExtension

noncomputable section
namespace HereditaryAtomicity.DVRBase.BlockInput
open scoped NNReal

variable {K k E : Type*} [Field K] [NontriviallyNormedField k] [CompleteSpace k]
  [NormedField E] [NormedAlgebra k E] {R : Subring K} {π : R} {t : ℕ → R}
  (I : BlockInput R k E π t) (w : Valuation K ℝ≥0)
  (hw : ∀ r : R, I.valuation (I.embedding r) = w (r : K))

local notation "D" => I.toSourceBlockData BlockState.basisLoss w hw

/-- The actual block construction supplies H3 in the literal source-data
coordinates, with its actual moving degree and selected previous-basis loss. -/
theorem actual_product_degree_growth (j : ℕ) :
    3 * ((D).exponent : ℝ) *
      (2 * (D).threshold (j + 1) + I.omega BlockState.basisLoss j) ≤
        (movingDegree k (I.generator BlockState.basisLoss) j : ℝ) * (D).weight j := by
  rw [I.toSourceBlockData_threshold, I.toSourceBlockData_weight]
  exact I.degree_mul_blockOrder_ge BlockState.basisLoss j

/-- Lemma X's post-loss estimate for a literal product built from the actual
recursive blocks. Its degree-growth bound is a conclusion of the construction. -/
theorem actual_product_after_loss {O : Subring K} {N : ℕ}
    (πO : O) (hπ : (πO : K) = (π : K))
    (hO : ∀ a : O, w (a : K) ≤ 1)
    (p : (D).FormalProduct O N) (hc : p.coefficient ≠ 0)
    (i : Fin N) (value : ℝ)
    (hfail : correctedDigit p.formalExponent i ∉
      digitInterval (movingDegree k (I.generator BlockState.basisLoss) i.val))
    (hloss : levelValue (fun j : Fin N => (D).weight j.val) (D).exponent
        (realValuationOrder (coefficientFractionValuation O w) (p.formalCoefficient πO))
        p.formalExponent (p.checkCut i) - I.omega BlockState.basisLoss i.val ≤ value) :
    (D).threshold (p.checkCut i) + (D).endpointOrder (p.checkCut i) + (D).endpointOrder 1 < value := by
  exact p.after_loss πO hπ hO hc i
    (movingDegree k (I.generator BlockState.basisLoss) i.val)
    (I.omega BlockState.basisLoss i.val) value hfail
    (I.actual_product_degree_growth w hw i.val) hloss

/-- The same actual-block estimate with any normalized valuation on the
original coefficient fraction field, ready for a valuation-preserving map. -/
theorem actual_product_after_loss_of_valuation {O : Subring K} {N : ℕ}
    (πO : O) (v : Valuation (FractionRing O) ℝ≥0)
    (hπ : (πO : K) = (π : K))
    (hvπ : realValuationOrder v (algebraMap O (FractionRing O) πO) = 1)
    (hO : ∀ a : O, v (algebraMap O (FractionRing O) a) ≤ 1)
    (p : (D).FormalProduct O N) (hc : p.coefficient ≠ 0)
    (i : Fin N) (value : ℝ)
    (hfail : correctedDigit p.formalExponent i ∉
      digitInterval (movingDegree k (I.generator BlockState.basisLoss) i.val))
    (hloss : levelValue (fun j : Fin N => (D).weight j.val) (D).exponent
        (realValuationOrder v (p.formalCoefficient πO)) p.formalExponent (p.checkCut i) -
          I.omega BlockState.basisLoss i.val ≤ value) :
    (D).threshold (p.checkCut i) + (D).endpointOrder (p.checkCut i) + (D).endpointOrder 1 < value := by
  have hπ0 : πO ≠ 0 := by
    intro hz
    apply (D).uniformizer_ne_zero
    apply Subtype.ext
    change (π : K) = 0
    simpa only [hz, ZeroMemClass.coe_zero] using hπ.symm
  exact p.after_loss_of_valuation πO v hπ0 hvπ hO hc i
    (movingDegree k (I.generator BlockState.basisLoss) i.val)
    (I.omega BlockState.basisLoss i.val) value hfail
    (I.actual_product_degree_growth w hw i.val) hloss

end HereditaryAtomicity.DVRBase.BlockInput

noncomputable section
namespace HereditaryAtomicity.DVRBase
open scoped BigOperators NNReal

/-- Restricting the full prefix sum to its actual finite prefix changes only
its indexing type. -/
theorem kernel_prefixSum_eq_fin_sum {N l : ℕ} (h : l ≤ N) (f : Fin N → ℝ) :
    prefixSum f l = ∑ i : Fin l, f (Fin.castLE h i) := by
  classical
  symm
  apply Finset.sum_bij (fun i _ => Fin.castLE h i)
  · intro i _
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, i.isLt⟩
  · intro i _ j _ he
    exact Fin.castLE_injective h he
  · intro i hi
    exact ⟨⟨i.val, (Finset.mem_filter.mp hi).2⟩, Finset.mem_univ _, Fin.ext rfl⟩
  · intro i _
    rfl

/-- Above a shared tail, the difference of prefix orders stays fixed. -/
theorem kernel_prefixSum_sub_eq {N l k : ℕ} (hlk : l ≤ k) (hkN : k ≤ N)
    (f g : Fin N → ℝ) (htail : ∀ i : Fin N, l ≤ i.val → f i = g i) :
    prefixSum f k - prefixSum g k = prefixSum f l - prefixSum g l := by
  induction k with
  | zero =>
      have hl : l = 0 := Nat.eq_zero_of_le_zero hlk
      subst l
      rfl
  | succ k ih =>
      by_cases he : l = k + 1
      · subst l
        rfl
      · have hlk' : l ≤ k := by omega
        have hkN' : k < N := by omega
        rw [prefixSum_succ f hkN', prefixSum_succ g hkN', htail ⟨k, hkN'⟩ hlk']
        linarith only [ih hlk' (by omega)]

/-- The exact weighted total order of a coefficient and exponent at a prefix. -/
def kernelPrefixOrder {N l : ℕ} (h : l ≤ N) (u : Fin N → ℝ)
    (e : ℝ) (γ : Fin l → ℤ) : ℝ :=
  e + ∑ i : Fin l, (γ i : ℝ) * u (Fin.castLE h i)

/-- Replacing the corrected prefix changes the level value above that prefix
by exactly the change of its full monomial order. The common tail pole cancels. -/
theorem kernel_levelValue_splice_sub {N l k : ℕ} (h : l ≤ N)
    (hlk : l ≤ k) (hkN : k ≤ N) (u : Fin N → ℝ) (κ e d : ℝ)
    (β : Fin N → ℤ) (γ : Fin l → ℤ) :
    levelValue u κ d (splicePrefix h β γ) k - levelValue u κ e β k =
      kernelPrefixOrder h u d γ - kernelPrefixOrder h u e (shiftedPrefix h β) := by
  have hdiff := kernel_prefixSum_sub_eq hlk hkN
    (fun i => (splicePrefix h β γ i : ℝ) * u i)
    (fun i => (β i : ℝ) * u i) (by
      intro i hi
      rw [splicePrefix_tail h β γ i hi])
  rw [kernel_prefixSum_eq_fin_sum h, kernel_prefixSum_eq_fin_sum h] at hdiff
  have hsum :
      (∑ i : Fin l, (splicePrefix h β γ (Fin.castLE h i) : ℝ) * u (Fin.castLE h i)) -
          ∑ i : Fin l, (β (Fin.castLE h i) : ℝ) * u (Fin.castLE h i) =
        (∑ i : Fin l, (γ i : ℝ) * u (Fin.castLE h i)) -
          ∑ i : Fin l, (shiftedPrefix h β i : ℝ) * u (Fin.castLE h i) := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    simp only [splicePrefix, Fin.val_castLE, dite_eq_left i.isLt, shiftedPrefix,
      Int.cast_sub, Int.cast_add]
    ring
  rw [hsum] at hdiff
  simp only [levelValue, partialValue, poleTail_splicePrefix h β γ hlk, kernelPrefixOrder]
  linarith only [hdiff]

/-- A prefix coordinate estimate gives the exact loss bound at every later
check cut, even when that cut is larger than the last failed window. -/
theorem kernel_levelValue_splice_lower {N l k : ℕ} (h : l ≤ N)
    (hlk : l ≤ k) (hkN : k ≤ N) (u : Fin N → ℝ) (κ e d Ω : ℝ)
    (β : Fin N → ℤ) (γ : Fin l → ℤ)
    (hbound : kernelPrefixOrder h u e (shiftedPrefix h β) - Ω ≤
      kernelPrefixOrder h u d γ) :
    levelValue u κ e β k - Ω ≤ levelValue u κ d (splicePrefix h β γ) k := by
  have he := kernel_levelValue_splice_sub h hlk hkN u κ e d β γ
  linarith only [he, hbound]

/-- A bad moving exponent has a largest failed coordinate, so its suffix is
already in the required moving windows. -/
theorem kernel_exists_largest_failed_digit {N : ℕ} (D : Fin N → ℕ)
    (β : Fin N → ℤ) (hbad : ¬ IsWindowExponent D β) :
    ∃ i : Fin N, correctedDigit β i ∉ digitInterval (D i) ∧
      ∀ j : Fin N, i.val + 1 ≤ j.val → correctedDigit β j ∈ digitInterval (D j) := by
  classical
  change ¬ ∀ i, correctedDigit β i ∈ digitInterval (D i) at hbad
  obtain ⟨i, hi⟩ := not_forall.mp hbad
  let s := Finset.univ.filter (fun j : Fin N => correctedDigit β j ∉ digitInterval (D j))
  have hs : s.Nonempty := ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩
  refine ⟨s.max' hs, (Finset.mem_filter.mp (Finset.max'_mem s hs)).2, ?_⟩
  intro j hj
  by_contra hfail
  have hle : j ≤ s.max' hs := Finset.le_max' s j
    (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hfail⟩)
  have hle' : j.val ≤ (s.max' hs).val := hle
  omega



section ActualResidual

variable (k : Type*) {E : Type*} [NormedField k] [NormedField E] [NormedAlgebra k E]

/-- The actual lift of a monomial is the lower-level expansion spliced into
its unchanged suffix. Taking the common scalar to be one makes the coefficient
of each spliced term exactly the lower basis coordinate. -/
theorem kernel_movingLift_single_eq_sum (y : ℕ → Eˣ)
    (hy : ∀ i, IsAlgebraic k (y i : E)) {l N : ℕ} (h : l ≤ N)
    (β : Fin N → ℤ)
    (htail : ∀ i : Fin N, l ≤ i.val → correctedDigit β i ∈ digitInterval (movingDegree k y i.val))
    (c : k) :
    movingTowerLift k y hy N (movingTowerEval k y N (AddMonoidAlgebra.single β c)) =
      ∑ γ ∈ ((movingTowerBasis k y hy l).repr
          (c • movingMonomial k y l (shiftedPrefix h β))).support,
        AddMonoidAlgebra.single (splicePrefix h β γ.val)
          ((movingTowerBasis k y hy l).repr
            (c • movingMonomial k y l (shiftedPrefix h β)) γ) := by
  rw [movingTowerLift_eval_single_peeling k y hy h β htail c 1 one_ne_zero,
    div_one, movingTowerEval_single, movingTowerLift_eq_sum, map_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro γ _
  rw [prefixLaurentMap_single_mul_peeling, mul_one]

/-- Exact additive membership of a bad-term residual follows from membership
of its original monomial and all actual peeled coordinate monomials. -/
theorem kernel_moving_residual_mem (y : ℕ → Eˣ)
    (hy : ∀ i, IsAlgebraic k (y i : E)) {l N : ℕ} (h : l ≤ N)
    (β : Fin N → ℤ)
    (htail : ∀ i : Fin N, l ≤ i.val → correctedDigit β i ∈ digitInterval (movingDegree k y i.val))
    (c : k) (J : AddSubgroup (Laurent k N))
    (horiginal : AddMonoidAlgebra.single β c ∈ J)
    (hcoordinates : ∀ γ : WindowExponent (fun i : Fin l => movingDegree k y i.val),
      (movingTowerBasis k y hy l).repr
          (c • movingMonomial k y l (shiftedPrefix h β)) γ ≠ 0 →
        AddMonoidAlgebra.single (splicePrefix h β γ.val)
          ((movingTowerBasis k y hy l).repr
            (c • movingMonomial k y l (shiftedPrefix h β)) γ) ∈ J) :
    AddMonoidAlgebra.single β c -
      movingTowerLift k y hy N (movingTowerEval k y N (AddMonoidAlgebra.single β c)) ∈ J := by
  apply J.sub_mem horiginal
  rw [kernel_movingLift_single_eq_sum k y hy h β htail c]
  apply J.sum_mem
  intro γ hγ
  exact hcoordinates γ (Finsupp.mem_support_iff.mp hγ)

/-- A finite list presentation retains repeated product terms when decomposing
an actual evaluation-kernel element into its moving-basis residuals. -/
theorem kernel_moving_decomposition_list (y : ℕ → Eˣ)
    (hy : ∀ i, IsAlgebraic k (y i : E)) (N : ℕ) {ι : Type*}
    (ps : List ι) (f : ι → Laurent k N)
    (hzero : movingTowerEval k y N ((ps.map f).sum) = 0) :
    (ps.map f).sum = (ps.map (fun p => f p -
      movingTowerLift k y hy N (movingTowerEval k y N (f p)))).sum := by
  have he : (ps.map (fun p => f p -
      movingTowerLift k y hy N (movingTowerEval k y N (f p)))).sum =
        (ps.map f).sum - movingTowerLift k y hy N (movingTowerEval k y N ((ps.map f).sum)) := by
    clear hzero
    induction ps with
    | nil => simp
    | cons p ps ih =>
        simp only [List.map_cons, List.sum_cons, map_add, ih]
        abel
  rw [he, hzero, map_zero, sub_zero]

end ActualResidual

section SelectedCoordinates

variable {R k E : Type*} [CommRing R] [IsDomain R]
  [NontriviallyNormedField k] [CompleteSpace k] [NormedField E]
  [NormedAlgebra k E] [IsUltrametricDist E] {π : R} {t : ℕ → R}
  (I : BlockInput R k E π t)

/-- The monomial basis bound of the actual recursively chosen blocks controls each spliced
coefficient at the numerical check cut, with the exact previously selected loss. -/
theorem BlockInput.kernel_spliced_level_lower
    (v : Valuation k ℝ≥0) (hv : ∀ a : k, realValuationOrder v a = -Real.log ‖a‖)
    {N : ℕ} (u : Fin N → ℝ)
    (hu : ∀ j : Fin N, u j = -Real.log ‖(I.generator BlockState.basisLoss j.val : E)‖)
    (i : Fin N) (β : Fin N → ℤ) (c : k) (hc : c ≠ 0)
    (γ : WindowExponent
      (fun j : Fin (i.val + 1) => movingDegree k (I.generator BlockState.basisLoss) j.val))
    (hγ : (movingTowerBasis k (I.generator BlockState.basisLoss)
      (I.generator_algebraic BlockState.basisLoss) (i.val + 1)).repr
        (c • movingMonomial k (I.generator BlockState.basisLoss) (i.val + 1)
          (shiftedPrefix i.isLt β)) γ ≠ 0)
    {q : ℕ} (hiq : i.val + 1 ≤ q) (hqN : q ≤ N) :
    levelValue u I.chain.exponent (realValuationOrder v c) β q -
        I.omega BlockState.basisLoss i.val ≤
      levelValue u I.chain.exponent
        (realValuationOrder v ((movingTowerBasis k (I.generator BlockState.basisLoss)
          (I.generator_algebraic BlockState.basisLoss) (i.val + 1)).repr
            (c • movingMonomial k (I.generator BlockState.basisLoss) (i.val + 1)
              (shiftedPrefix i.isLt β)) γ))
        (splicePrefix i.isLt β γ.val) q := by
  apply kernel_levelValue_splice_lower i.isLt hiq hqN
  have hb := I.selected_monomial_order_bound i.val c (shiftedPrefix i.isLt β) γ hγ
  rw [order_movingMonomial_eq_sum k _ _ _ c hc,
    order_movingTowerBasis_term_eq_sum k _ _ _ γ _ hγ] at hb
  simpa only [kernelPrefixOrder, hv, hu, Fin.val_castLE] using hb

end SelectedCoordinates

namespace SourceBlockData

variable {K k E : Type*} [Field K] [NontriviallyNormedField k] [CompleteSpace k]
  [NormedField E] [NormedAlgebra k E] [IsUltrametricDist E]
  {R : Subring K} (D : SourceBlockData R)

/-- A formal product residual lies in `Z₁J₀` for any block sequence with
admissible previous-basis bounds and the degree-growth inequality. The supplied bounds need not be the
constants selected by the recursive construction. -/
theorem kernel_product_residual_mem_of_growth
    (y : ℕ → Eˣ) (hy : ∀ j, IsAlgebraic k (y j : E))
    (hweight : ∀ j, D.weight j = -Real.log ‖(y j : E)‖)
    (C : ℕ → ℝ) (hC : ∀ j, 1 ≤ C j)
    (hb : ∀ j (z : movingField k y j) i,
      ‖(movingTowerBasis k y hy j).repr z i • movingTowerBasis k y hy j i‖ ≤ C j * ‖z‖)
    (hgrowth : ∀ j, 3 * (D.exponent : ℝ) * (2 * D.threshold (j + 1) + Real.log (C j)) ≤
      (movingDegree k y j : ℝ) * D.weight j)
    {O : Subring K} (πO : O) (hπ : (πO : K) = (D.uniformizer : K))
    (hO : ∀ a : O, D.valuation (a : K) ≤ 1)
    (v : Valuation k ℝ≥0) (hv : ∀ a : k, realValuationOrder v a = -Real.log ‖a‖)
    (f : FractionRing O →+* k)
    (hf : ∀ a, v (f a) = coefficientFractionValuation O D.valuation a)
    {N : ℕ} (p : D.FormalProduct O N) :
    AddMonoidAlgebra.single p.formalExponent (f (p.formalCoefficient πO)) -
        movingTowerLift k y hy N (movingTowerEval k y N
          (AddMonoidAlgebra.single p.formalExponent (f (p.formalCoefficient πO)))) ∈
      modelKernelJunk v (f (algebraMap O (FractionRing O) πO)) (D.modelParameters N) := by
  classical
  have hπ0 : πO ≠ 0 := by
    intro hz
    apply D.uniformizer_ne_zero
    apply Subtype.ext
    change (D.uniformizer : K) = 0
    simpa only [hz, ZeroMemClass.coe_zero] using hπ.symm
  have hπk0 : f (algebraMap O (FractionRing O) πO) ≠ 0 :=
    (map_ne_zero_iff f f.injective).mpr (D.coefficientUniformizer_ne_zero O πO hπ)
  have horder (a : FractionRing O) :
      realValuationOrder v (f a) =
        realValuationOrder (coefficientFractionValuation O D.valuation) a := by
    simp only [realValuationOrder, hf]
  have hπk : realValuationOrder v (f (algebraMap O (FractionRing O) πO)) = 1 := by
    rw [horder]
    exact D.coefficientUniformizer_order O πO hπ
  have hafter : ∀ (hc : p.coefficient ≠ 0) (i : Fin N) (value : ℝ)
      (hfail : correctedDigit p.formalExponent i ∉ digitInterval (movingDegree k y i.val))
      (hloss : levelValue (fun j : Fin N => D.weight j.val) D.exponent
        (realValuationOrder (coefficientFractionValuation O D.valuation) (p.formalCoefficient πO))
        p.formalExponent (p.checkCut i) - Real.log (C i.val) ≤ value),
      D.threshold (p.checkCut i) + D.endpointOrder (p.checkCut i) + D.endpointOrder 1 < value :=
    fun hc i value hfail hloss =>
      p.after_loss πO hπ hO hc i (movingDegree k y i.val) (Real.log (C i.val)) value hfail
        (hgrowth i.val) hloss
  by_cases hc : p.coefficient = 0
  · have hz : p.formalCoefficient πO = 0 := by
      simp [SourceBlockData.FormalProduct.formalCoefficient, hc]
    simp only [hz, map_zero, AddMonoidAlgebra.single_zero, sub_self]
    exact AddSubgroup.zero_mem _
  · have hc' : f (p.formalCoefficient πO) ≠ 0 :=
      (map_ne_zero_iff f f.injective).mpr (p.formalCoefficient_ne_zero πO hπ0 hc)
    by_cases hwindow : IsWindowExponent (fun j : Fin N => movingDegree k y j.val) p.formalExponent
    · rw [movingTowerLift_eval_single k y hy N p.formalExponent hwindow]
      simpa only [sub_self] using
        (modelKernelJunk v (f (algebraMap O (FractionRing O) πO)) (D.modelParameters N)).zero_mem
    · obtain ⟨i, hfail, htail⟩ := kernel_exists_largest_failed_digit _ p.formalExponent hwindow
      let first : Fin N := ⟨0, by have hi := i.isLt; omega⟩
      have hqpos : 0 < p.checkCut i :=
        (Nat.succ_pos i.val).trans_le (p.failedCut_le_checkCut i)
      have hcriterion (β : Fin N → ℤ) (d : k) (hd : d ≠ 0)
          (hvalue : D.threshold (p.checkCut i) + D.endpointOrder (p.checkCut i) +
            D.endpointOrder 1 <
              levelValue (fun j : Fin N => D.weight j.val) D.exponent
                (realValuationOrder v d) β (p.checkCut i)) :
          AddMonoidAlgebra.single β d ∈
            modelKernelJunk v (f (algebraMap O (FractionRing O) πO)) (D.modelParameters N) := by
        apply modelKernelJunk_single_of_criterion v _ hπk0 hπk (D.modelParameters N)
          β d hd first rfl hqpos (p.checkCut_le i)
        change D.threshold (p.checkCut i) +
          remainingValue (fun j : Fin N => D.weight j.val) D.exponent (p.checkCut i) +
          remainingValue (fun j : Fin N => D.weight j.val) D.exponent 1 ≤ _
        rw [← D.endpointOrder_eq_remainingValue N (p.checkCut i) (p.checkCut_le i),
          ← D.endpointOrder_eq_remainingValue N 1 (by have hi := i.isLt; omega)]
        exact hvalue.le
      apply kernel_moving_residual_mem k y hy i.isLt p.formalExponent htail
        (f (p.formalCoefficient πO)) _
      · apply hcriterion _ _ hc'
        apply hafter hc i _ hfail
        rw [← horder]
        exact sub_le_self _ (Real.log_nonneg (hC i.val))
      · intro γ hγ
        apply hcriterion _ _ hγ
        apply hafter hc i _ hfail
        rw [← horder]
        apply kernel_levelValue_splice_lower i.isLt (p.failedCut_le_checkCut i) (p.checkCut_le i)
        have hbd := order_movingTowerBasis_monomial_term_ge k y hy i.val (hC i.val) (hb i.val)
          (f (p.formalCoefficient πO)) (shiftedPrefix i.isLt p.formalExponent) γ hγ
        rw [order_movingMonomial_eq_sum k _ _ _ _ hc',
          order_movingTowerBasis_term_eq_sum k _ _ _ γ _ hγ] at hbd
        simpa only [kernelPrefixOrder, hv, hweight, Fin.val_castLE] using hbd

/-- The evaluation-kernel bound for arbitrary blocks satisfying the degree-growth inequality with an admissible basis constant. -/
theorem kernel_formal_mem_of_growth
    (y : ℕ → Eˣ) (hy : ∀ j, IsAlgebraic k (y j : E))
    (hweight : ∀ j, D.weight j = -Real.log ‖(y j : E)‖)
    (C : ℕ → ℝ) (hC : ∀ j, 1 ≤ C j)
    (hb : ∀ j (z : movingField k y j) i,
      ‖(movingTowerBasis k y hy j).repr z i • movingTowerBasis k y hy j i‖ ≤ C j * ‖z‖)
    (hgrowth : ∀ j, 3 * (D.exponent : ℝ) * (2 * D.threshold (j + 1) + Real.log (C j)) ≤
      (movingDegree k y j : ℝ) * D.weight j)
    {O : Subring K} (πO : O) (hπ : (πO : K) = (D.uniformizer : K))
    (hO : ∀ a : O, D.valuation (a : K) ≤ 1)
    (v : Valuation k ℝ≥0) (hv : ∀ a : k, realValuationOrder v a = -Real.log ‖a‖)
    (f : FractionRing O →+* k)
    (hf : ∀ a, v (f a) = coefficientFractionValuation O D.valuation a)
    {N : ℕ} (q : Laurent (FractionRing O) N) (hq : q ∈ D.formalRing O πO N)
    (hzero : movingTowerEval k y N (laurentMap f N q) = 0) :
    laurentMap f N q ∈
      modelKernelJunk v (f (algebraMap O (FractionRing O) πO)) (D.modelParameters N) := by
  obtain ⟨ps, hps⟩ := D.formalRing_exists_products O πO hq
  have hmap : (ps.map (fun p => laurentMap f N (p.formal πO))).sum = laurentMap f N q := by
    have h := congrArg (laurentMap f N) hps
    simpa only [map_list_sum, List.map_map, Function.comp_def] using h
  rw [← hmap]
  rw [kernel_moving_decomposition_list k y hy N ps (fun p => laurentMap f N (p.formal πO))
    (by rwa [hmap])]
  apply AddSubgroup.list_sum_mem
  intro x hx
  obtain ⟨p, _, rfl⟩ := List.mem_map.mp hx
  rw [p.formal_eq_single, laurentMap_single]
  exact D.kernel_product_residual_mem_of_growth y hy hweight C hC hb hgrowth πO hπ hO v hv f hf p


end SourceBlockData

section SourceResidual

variable {K k E : Type*} [Field K] [NontriviallyNormedField k] [CompleteSpace k]
  [NormedField E] [NormedAlgebra k E] [IsUltrametricDist E]
  {R : Subring K} {π : R} {t : ℕ → R}
  (I : BlockInput R k E π t) (w : Valuation K ℝ≥0)
  (hw : ∀ r : R, I.valuation (I.embedding r) = w (r : K))
  (hcompat : ∀ x : E, realValuationOrder I.valuation x = -Real.log ‖x‖)

local notation "D" => I.toSourceBlockData BlockState.basisLoss w hw
local notation "y" => I.generator BlockState.basisLoss
local notation "hy" => I.generator_algebraic BlockState.basisLoss

include hcompat

omit [IsUltrametricDist E] in
/-- The literal source weight is exactly the norm order of the actual selected
ambient generator. -/
theorem BlockInput.kernel_source_weight_norm (j : ℕ) :
    (D).weight j = -Real.log ‖(y j : E)‖ := by
  rw [I.toSourceBlockData_weight]
  change realValuationOrder I.valuation (I.embedding (I.sourceY BlockState.basisLoss j)) = _
  rw [← I.generator_val_eq_embedding_sourceY]
  exact hcompat (y j)

/-- Every product term's moving-basis residual belongs to the actual additive
image Z₁J₀. All products, degrees, thresholds and basis losses come from the
constructed source blocks. -/
theorem BlockInput.kernel_product_residual_mem
    {O : Subring K} (πO : O) (hπ : (πO : K) = (π : K))
    (hO : ∀ a : O, w (a : K) ≤ 1)
    (v : Valuation k ℝ≥0) (hv : ∀ a : k, realValuationOrder v a = -Real.log ‖a‖)
    (f : FractionRing O →+* k)
    (hf : ∀ a, v (f a) = coefficientFractionValuation O w a)
    {N : ℕ} (p : (D).FormalProduct O N) :
    AddMonoidAlgebra.single p.formalExponent (f (p.formalCoefficient πO)) -
        movingTowerLift k y hy N (movingTowerEval k y N
          (AddMonoidAlgebra.single p.formalExponent (f (p.formalCoefficient πO)))) ∈
      modelKernelJunk v (f (algebraMap O (FractionRing O) πO)) ((D).modelParameters N) := by
  exact (D).kernel_product_residual_mem_of_growth y hy
    (I.kernel_source_weight_norm w hw hcompat) I.selectedBasisConstant
    I.one_le_selectedBasisConstant I.selectedBasisConstant_spec
    (fun j => by
      rw [← I.omega_basisLoss_eq_log]
      exact I.actual_product_degree_growth w hw j)
    πO hπ hO v hv f hf p

/-- Full kernel control for the original finite source-generator ring after
an explicit valuation-preserving coefficient extension. Membership in Z₁J₀
is exact additive-subgroup membership, derived term by term before collecting. -/
theorem BlockInput.kernel_formal_mem
    {O : Subring K} (πO : O) (hπ : (πO : K) = (π : K))
    (hO : ∀ a : O, w (a : K) ≤ 1)
    (v : Valuation k ℝ≥0) (hv : ∀ a : k, realValuationOrder v a = -Real.log ‖a‖)
    (f : FractionRing O →+* k)
    (hf : ∀ a, v (f a) = coefficientFractionValuation O w a)
    {N : ℕ} (q : Laurent (FractionRing O) N) (hq : q ∈ (D).formalRing O πO N)
    (hzero : movingTowerEval k y N (laurentMap f N q) = 0) :
    laurentMap f N q ∈
      modelKernelJunk v (f (algebraMap O (FractionRing O) πO)) ((D).modelParameters N) := by
  exact (D).kernel_formal_mem_of_growth y hy
    (I.kernel_source_weight_norm w hw hcompat) I.selectedBasisConstant
    I.one_le_selectedBasisConstant I.selectedBasisConstant_spec
    (fun j => by
      rw [← I.omega_basisLoss_eq_log]
      exact I.actual_product_degree_growth w hw j)
    πO hπ hO v hv f hf q hq hzero

/-- Both conclusions of Lemma X for the actual finite source ring and its
literal moving-evaluation kernel. -/
theorem BlockInput.formal_model_and_kernel_control
    {O : Subring K} (πO : O) (hπ : (πO : K) = (π : K))
    (hO : ∀ a : O, w (a : K) ≤ 1)
    (v : Valuation k ℝ≥0) (hv : ∀ a : k, realValuationOrder v a = -Real.log ‖a‖)
    (f : FractionRing O →+* k)
    (hf : ∀ a, v (f a) = coefficientFractionValuation O w a) (N : ℕ) :
    ((D).formalRing O πO N).map (laurentMap f N) ≤
        modelRing v (f (algebraMap O (FractionRing O) πO)) ((D).modelParameters N) ∧
      ∀ q ∈ (D).formalRing O πO N,
        movingTowerEval k y N (laurentMap f N q) = 0 →
          laurentMap f N q ∈
            modelKernelJunk v (f (algebraMap O (FractionRing O) πO)) ((D).modelParameters N) := by
  constructor
  · rintro p ⟨q, hq, rfl⟩
    exact laurentMap_mem_modelRing f (coefficientFractionValuation O w) v hf _ _
      ((D).formalRing_le_modelRing O πO hπ hO N hq)
  · intro q hq hzero
    exact I.kernel_formal_mem w hw hcompat πO hπ hO v hv f hf q hq hzero

end SourceResidual

end HereditaryAtomicity.DVRBase
