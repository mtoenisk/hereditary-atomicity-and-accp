import HereditaryAtomicity.DVRBase.SourceBlockAdapter

/-!
# Prescribed return-exponent floors

The next exponent may be required to exceed any natural-number bound depending
on the preceding stage and its finite history. The exponent is enlarged before
the new block degree is chosen, so the original growth estimate is retained.
-/

noncomputable section
open scoped NNReal BigOperators
namespace HereditaryAtomicity.DVRBase.BlockInput

variable {R k L : Type*} [CommRing R] [IsDomain R]
  [Field k] [Field L] [Algebra k L] {π : R} {t : ℕ → R}
  (I : BlockInput R k L π t) (loss : ℕ → BlockState k L → ℝ)
  (floor : ℕ → BlockState k L → ℕ)

/-- A stage choice with a prescribed lower bound on its return exponent. -/
structure FloorChoice (n : ℕ) (s : BlockState k L) extends I.Choice loss n s where
  power_ge : floor n s ≤ power

/-- Every stage admits the requested exponent floor. Its degree is selected
only after both the enlarged exponent and the old basis loss are fixed. -/
theorem floorChoice_nonempty (n : ℕ) (s : BlockState k L) :
    Nonempty (I.FloorChoice loss floor n s) := by
  let : FiniteDimensional k (movingField k s.values n) :=
    movingField_finiteDimensional k s.values s.algebraic n
  obtain ⟨e, he, heq⟩ := I.chain.ratio_power s.index
  let e' := max e (floor n s)
  have he' : 0 < e' := he.trans_le (le_max_left _ _)
  have hreturn : π ^ I.chain.exponent ∣ t s.index ^ e' :=
    heq.trans (pow_dvd_pow _ (le_max_left _ _))
  obtain ⟨m, hm⟩ := I.chain.exists_sourceBlock_degree_mul_ge k
    (movingField k s.values n) L I.embedding I.embedding_injective I.valuation
    I.coefficient_orders I.source_algebraic I.endpoint_order_ge_one I.ratio_positive
    s.index (3 * (I.chain.exponent : ℝ) *
      (2 * (s.threshold + 2 * I.chain.exponent * e') + loss n s))
  exact ⟨⟨⟨e', he', hreturn, m, hm⟩, le_max_right _ _⟩⟩

/-- Choose an exponent meeting the requested floor before adjoining a block. -/
def floorChoose (n : ℕ) (s : BlockState k L) : I.FloorChoice loss floor n s :=
  Classical.choice (I.floorChoice_nonempty loss floor n s)

/-- The finite-history recursion with a stage-dependent exponent floor. -/
def floorState : ℕ → BlockState k L
  | 0 => initial (k := k) (L := L)
  | n + 1 => I.advance loss n (floorState n)
      (I.floorChoose loss floor n (floorState n)).toChoice

def floorIndex (n : ℕ) : ℕ := (I.floorState loss floor n).index

def floorLength (n : ℕ) : ℕ :=
  (I.floorChoose loss floor n (I.floorState loss floor n)).length

def floorReturnExponent (n : ℕ) : ℕ :=
  (I.floorChoose loss floor n (I.floorState loss floor n)).power

def floorThreshold (n : ℕ) : ℝ := (I.floorState loss floor n).threshold

def floorOmega (n : ℕ) : ℝ := loss n (I.floorState loss floor n)

def floorGenerator (n : ℕ) : Lˣ :=
  I.blockUnit (I.floorIndex loss floor n) (I.floorLength loss floor n)

@[simp] theorem floorIndex_zero : I.floorIndex loss floor 0 = 0 := rfl

@[simp] theorem floorIndex_succ (n : ℕ) :
    I.floorIndex loss floor (n + 1) =
      I.floorIndex loss floor n + I.floorLength loss floor n + 1 := rfl

@[simp] theorem floorThreshold_zero : I.floorThreshold loss floor 0 = 0 := rfl

@[simp] theorem floorThreshold_succ (n : ℕ) :
    I.floorThreshold loss floor (n + 1) = I.floorThreshold loss floor n +
      2 * I.chain.exponent * I.floorReturnExponent loss floor n := rfl

theorem floorIndex_strictMono : StrictMono (I.floorIndex loss floor) := by
  apply strictMono_nat_of_lt_succ
  intro n
  rw [I.floorIndex_succ]
  omega

theorem floorReturnExponent_pos (n : ℕ) : 0 < I.floorReturnExponent loss floor n :=
  (I.floorChoose loss floor n (I.floorState loss floor n)).power_pos

/-- The requested floor holds at every actual recursive stage. -/
theorem floorReturnExponent_ge (n : ℕ) :
    floor n (I.floorState loss floor n) ≤ I.floorReturnExponent loss floor n :=
  (I.floorChoose loss floor n (I.floorState loss floor n)).power_ge

theorem floorReturnExponent_spec (n : ℕ) :
    π ^ I.chain.exponent ∣ t (I.floorIndex loss floor n) ^
      I.floorReturnExponent loss floor n :=
  (I.floorChoose loss floor n (I.floorState loss floor n)).power_return

theorem floorGenerator_algebraic (n : ℕ) :
    IsAlgebraic k (I.floorGenerator loss floor n : L) :=
  I.source_algebraic (sourceBlock t (I.floorIndex loss floor n) (I.floorLength loss floor n))

theorem floorState_prefix (n : ℕ) :
    ∀ i < n, (I.floorState loss floor n).values i = I.floorGenerator loss floor i := by
  induction n with
  | zero => intro i hi; omega
  | succ n ih =>
      intro i hi
      by_cases h : i = n
      · subst i
        exact Function.update_self _ _ _
      · have hi' : i < n := by omega
        change Function.update (I.floorState loss floor n).values n
          (I.floorGenerator loss floor n) i = _
        rw [Function.update_of_ne h]
        exact ih i hi'

theorem floorField_eq_state (n : ℕ) :
    movingField k (I.floorGenerator loss floor) n =
      movingField k (I.floorState loss floor n).values n :=
  movingField_congr_prefix k (fun i hi => (I.floorState_prefix loss floor n i hi).symm)

/-- The prescribed floor retains the actual moving-field degree inequality. -/
theorem floor_degree_mul_first_ratio_ge (n : ℕ) :
    3 * (I.chain.exponent : ℝ) *
      (2 * I.floorThreshold loss floor (n + 1) + I.floorOmega loss floor n) ≤
    (movingDegree k (I.floorGenerator loss floor) n : ℝ) *
      realValuationOrder I.valuation (I.embedding (t (I.floorIndex loss floor n))) := by
  have h := (I.floorChoose loss floor n (I.floorState loss floor n)).growth
  have hdegree : movingDegree k (I.floorGenerator loss floor) n =
      Module.finrank (movingField k (I.floorState loss floor n).values n)
        (IntermediateField.adjoin (movingField k (I.floorState loss floor n).values n)
          {I.embedding (sourceBlock t (I.floorIndex loss floor n) (I.floorLength loss floor n))}) := by
    dsimp only [movingDegree]
    rw [I.floorField_eq_state loss floor n]
    exact (IntermediateField.adjoin.finrank
      ((I.floorGenerator_algebraic loss floor n).tower_top
        (movingField k (I.floorState loss floor n).values n)).isIntegral).symm
  rw [hdegree]
  exact h

/-- The selected block is a literal source element. -/
def floorSourceY (n : ℕ) : R := sourceBlock t (I.floorIndex loss floor n) (I.floorLength loss floor n)

/-- The selected endpoint is a literal endpoint of the original chain. -/
def floorSourceZ (n : ℕ) : R := I.chain.endpoint (I.floorIndex loss floor n)

def floorBlockOrder (n : ℕ) : ℝ := realValuationOrder I.valuation (I.embedding (I.floorSourceY loss floor n))

def floorEndpointOrder (n : ℕ) : ℝ :=
  realValuationOrder I.valuation (I.embedding (I.floorSourceZ loss floor n))

@[simp] theorem floorGenerator_val_eq_embedding_sourceY (n : ℕ) :
    (I.floorGenerator loss floor n : L) = I.embedding (I.floorSourceY loss floor n) := rfl

theorem floorSourceY_ne_zero (n : ℕ) : I.floorSourceY loss floor n ≠ 0 :=
  I.chain.sourceBlock_ne_zero (I.floorIndex loss floor n) (I.floorLength loss floor n)

theorem floorSourceZ_ne_zero (n : ℕ) : I.floorSourceZ loss floor n ≠ 0 :=
  I.chain.endpoint_ne_zero (I.floorIndex loss floor n)

@[simp] theorem floorSourceZ_zero : I.floorSourceZ loss floor 0 = π ^ I.chain.exponent := by
  exact I.chain.top

theorem floorSourceZ_step (n : ℕ) :
    I.floorSourceZ loss floor n = I.floorSourceZ loss floor (n + 1) * I.floorSourceY loss floor n :=
  I.chain.selected_sourceBlock_step (I.floorIndex loss floor) (I.floorLength loss floor)
    (I.floorIndex_succ loss floor) n

/-- The previously chosen return exponent works for the selected whole
block inside the source ring. -/
theorem floorSourceY_power_return (n : ℕ) :
    π ^ I.chain.exponent ∣ I.floorSourceY loss floor n ^ I.floorReturnExponent loss floor n :=
  I.chain.sourceBlock_power_return (I.floorIndex loss floor n) (I.floorLength loss floor n)
    (I.floorReturnExponent loss floor n) (I.floorReturnExponent_spec loss floor n)

theorem floorSourceY_power_return_pos (n : ℕ) :
    0 < I.floorReturnExponent loss floor n ∧
      π ^ I.chain.exponent ∣ I.floorSourceY loss floor n ^ I.floorReturnExponent loss floor n :=
  ⟨I.floorReturnExponent_pos loss floor n, I.floorSourceY_power_return loss floor n⟩

theorem floorEndpointOrder_eq_exponent_sub_sum (n : ℕ) :
    I.floorEndpointOrder loss floor n = (I.chain.exponent : ℝ) -
      ∑ j ∈ Finset.range n, I.floorBlockOrder loss floor j := by
  exact I.chain.selected_endpoint_order_eq_sub_sum I.embedding I.embedding_injective
    I.valuation I.uniformizer_order (I.floorIndex loss floor) (I.floorLength loss floor)
    (I.floorIndex_zero loss floor)
      (I.floorIndex_succ loss floor) n

theorem floorOne_le_endpointOrder (n : ℕ) : 1 ≤ I.floorEndpointOrder loss floor n :=
  I.endpoint_order_ge_one (I.floorIndex loss floor n)

theorem floorBlockOrder_bounds (n : ℕ) :
    realValuationOrder I.valuation (I.embedding (t (I.floorIndex loss floor n))) ≤
        I.floorBlockOrder loss floor n ∧
      0 < I.floorBlockOrder loss floor n ∧ I.floorBlockOrder loss floor n < I.chain.exponent :=
  I.chain.selected_block_order_bounds I.embedding I.embedding_injective I.valuation
    I.endpoint_order_ge_one I.uniformizer_order I.ratio_positive
    (I.floorIndex loss floor) (I.floorLength loss floor) n

theorem floorBlockOrder_pos (n : ℕ) : 0 < I.floorBlockOrder loss floor n :=
  (I.floorBlockOrder_bounds loss floor n).2.1

theorem floorBlockOrder_lt_exponent (n : ℕ) : I.floorBlockOrder loss floor n < I.chain.exponent :=
  (I.floorBlockOrder_bounds loss floor n).2.2

theorem floorThreshold_eq_sum (n : ℕ) :
    I.floorThreshold loss floor n = 2 * (I.chain.exponent : ℝ) *
      ∑ j ∈ Finset.range n, (I.floorReturnExponent loss floor j : ℝ) :=
  blockThreshold_eq_sum I.chain.exponent (I.floorReturnExponent loss floor) (I.floorThreshold loss floor)
    (I.floorThreshold_zero loss floor) (I.floorThreshold_succ loss floor) n

theorem floorThreshold_step_ge (n : ℕ) :
    I.floorThreshold loss floor n + 2 * I.chain.exponent ≤ I.floorThreshold loss floor (n + 1) :=
  blockThreshold_step_ge I.chain.exponent (I.floorReturnExponent loss floor) (I.floorThreshold loss floor)
    (Nat.cast_nonneg _) (I.floorReturnExponent_pos loss floor) (I.floorThreshold_succ loss floor) n

theorem floorThreshold_strictMono : StrictMono (I.floorThreshold loss floor) :=
  blockThreshold_strictMono I.chain.exponent (I.floorReturnExponent loss floor) (I.floorThreshold loss floor)
    (by exact_mod_cast I.chain.exponent_pos) (I.floorReturnExponent_pos loss floor)
      (I.floorThreshold_succ loss floor)

theorem floorThreshold_succ_ge (n : ℕ) :
    2 * I.chain.exponent ≤ I.floorThreshold loss floor (n + 1) :=
  blockThreshold_succ_ge I.chain.exponent (I.floorReturnExponent loss floor) (I.floorThreshold loss floor)
    (Nat.cast_nonneg _) (I.floorReturnExponent_pos loss floor) (I.floorThreshold_zero loss floor)
      (I.floorThreshold_succ loss floor) n

/-- H3 for the actual relative degree and the actual selected block order.
The threshold and basis-loss bound were fixed before this block was chosen. -/
theorem floorDegree_mul_blockOrder_ge (n : ℕ) :
    3 * (I.chain.exponent : ℝ) *
      (2 * I.floorThreshold loss floor (n + 1) + I.floorOmega loss floor n) ≤
        (movingDegree k (I.floorGenerator loss floor) n : ℝ) * I.floorBlockOrder loss floor n :=
  I.chain.sourceBlock_degree_mul_ge I.embedding I.embedding_injective I.valuation
    I.ratio_positive (I.floorIndex loss floor n) (I.floorLength loss floor n)
      (movingDegree k (I.floorGenerator loss floor) n) (I.floor_degree_mul_first_ratio_ge loss floor n)

end HereditaryAtomicity.DVRBase.BlockInput

namespace HereditaryAtomicity.DVRBase.BlockInput

variable {K k L : Type*} [Field K] [Field k] [Field L] [Algebra k L]
  {R : Subring K} {π : R} {t : ℕ → R}
  (I : BlockInput R k L π t) (loss : ℕ → BlockState k L → ℝ)
  (floor : ℕ → BlockState k L → ℕ)
  (w : Valuation K ℝ≥0) (hw : ∀ r : R, I.valuation (I.embedding r) = w (r : K))

/-- The floor-controlled recursion has the same literal source output contract. -/
def floorToSourceBlockData : SourceBlockData R where
  uniformizer := π
  uniformizer_ne_zero := by
    intro h
    have hn := I.uniformizer_order
    simp [h] at hn
  exponent := I.chain.exponent
  exponent_pos := I.chain.exponent_pos
  ratio := I.floorSourceY loss floor
  endpoint := I.floorSourceZ loss floor
  endpoint_ne_zero := I.floorSourceZ_ne_zero loss floor
  top := I.floorSourceZ_zero loss floor
  step := I.floorSourceZ_step loss floor
  valuation := w
  normalized := by
    simpa only [realValuationOrder, hw] using I.uniformizer_order
  ratio_order_pos n := by
    simpa only [floorBlockOrder, realValuationOrder, hw] using I.floorBlockOrder_pos loss floor n
  endpoint_order_ge_one n := by
    simpa only [floorEndpointOrder, realValuationOrder, hw] using I.floorOne_le_endpointOrder loss floor n
  returnExponent := I.floorReturnExponent loss floor
  returnExponent_pos := I.floorReturnExponent_pos loss floor
  power_return := I.floorSourceY_power_return loss floor

@[simp] theorem floorToSourceBlockData_ratio (n : ℕ) :
    (I.floorToSourceBlockData loss floor w hw).ratio n = I.floorSourceY loss floor n := rfl

@[simp] theorem floorToSourceBlockData_endpoint (n : ℕ) :
    (I.floorToSourceBlockData loss floor w hw).endpoint n = I.floorSourceZ loss floor n := rfl

theorem floorToSourceBlockData_weight (n : ℕ) :
    (I.floorToSourceBlockData loss floor w hw).weight n = I.floorBlockOrder loss floor n := by
  simp only [SourceBlockData.weight, floorToSourceBlockData, floorBlockOrder, realValuationOrder, hw]

theorem floorToSourceBlockData_threshold (n : ℕ) :
    (I.floorToSourceBlockData loss floor w hw).threshold n = I.floorThreshold loss floor n := by
  rw [I.floorThreshold_eq_sum]
  change 2 * (I.chain.exponent : ℝ) * ∑ i : Fin n, (I.floorReturnExponent loss floor i.val : ℝ) = _
  rw [Fin.sum_univ_eq_sum_range (fun j => (I.floorReturnExponent loss floor j : ℝ)) n]

end HereditaryAtomicity.DVRBase.BlockInput

namespace HereditaryAtomicity.DVRBase.BlockInput

variable {R k L : Type*} [CommRing R] [IsDomain R]
  [NontriviallyNormedField k] [CompleteSpace k] [NormedField L] [NormedAlgebra k L]
  {π : R} {t : ℕ → R} (I : BlockInput R k L π t)
  (floor : ℕ → BlockState k L → ℕ)

/-- The basis constant recorded before each floor-controlled degree choice. -/
def floorSelectedBasisConstant (n : ℕ) : ℝ :=
  (I.floorState BlockState.basisLoss floor n).basisConstant n

theorem one_le_floorSelectedBasisConstant (n : ℕ) :
    1 ≤ I.floorSelectedBasisConstant floor n :=
  (I.floorState BlockState.basisLoss floor n).one_le_basisConstant n

theorem floorOmega_basisLoss_eq_log (n : ℕ) :
    I.floorOmega BlockState.basisLoss floor n =
      Real.log (I.floorSelectedBasisConstant floor n) := rfl

/-- The preceding-history bound transports to the actual floor-selected tower. -/
theorem floorSelectedBasisConstant_spec (n : ℕ) :
    ∀ z : movingField k (I.floorGenerator BlockState.basisLoss floor) n, ∀ i,
      ‖(movingTowerBasis k (I.floorGenerator BlockState.basisLoss floor)
        (I.floorGenerator_algebraic BlockState.basisLoss floor) n).repr z i •
          movingTowerBasis k (I.floorGenerator BlockState.basisLoss floor)
            (I.floorGenerator_algebraic BlockState.basisLoss floor) n i‖ ≤
      I.floorSelectedBasisConstant floor n * ‖z‖ :=
  movingTowerBasis_norm_bound_congr_prefix k (I.floorState BlockState.basisLoss floor n).algebraic
    (I.floorGenerator_algebraic BlockState.basisLoss floor)
    (I.floorState_prefix BlockState.basisLoss floor n)
    ((I.floorState BlockState.basisLoss floor n).basisConstant_spec n)

end HereditaryAtomicity.DVRBase.BlockInput

namespace HereditaryAtomicity.DVRBase.BlockInput

variable {K k E : Type*} [Field K] [NontriviallyNormedField k] [CompleteSpace k]
  [NormedField E] [NormedAlgebra k E] {R : Subring K} {π : R} {t : ℕ → R}
  (I : BlockInput R k E π t) (floor : ℕ → BlockState k E → ℕ)
  (w : Valuation K ℝ≥0) (hw : ∀ r : R, I.valuation (I.embedding r) = w (r : K))

local notation "D" => I.floorToSourceBlockData BlockState.basisLoss floor w hw

/-- The degree-growth inequality for the literal source output of the recursion with prescribed floors. -/
theorem floor_actual_product_degree_growth (j : ℕ) :
    3 * ((D).exponent : ℝ) *
      (2 * (D).threshold (j + 1) + Real.log (I.floorSelectedBasisConstant floor j)) ≤
        (movingDegree k (I.floorGenerator BlockState.basisLoss floor) j : ℝ) * (D).weight j := by
  rw [I.floorToSourceBlockData_threshold, I.floorToSourceBlockData_weight,
    ← I.floorOmega_basisLoss_eq_log]
  exact I.floorDegree_mul_blockOrder_ge BlockState.basisLoss floor j

/-- The floor-selected source weight is the norm order used by kernel control. -/
theorem floor_source_weight_norm
    (hcompat : ∀ x : E, realValuationOrder I.valuation x = -Real.log ‖x‖) (j : ℕ) :
    (D).weight j = -Real.log ‖(I.floorGenerator BlockState.basisLoss floor j : E)‖ := by
  rw [I.floorToSourceBlockData_weight]
  change realValuationOrder I.valuation
    (I.embedding (I.floorSourceY BlockState.basisLoss floor j)) = _
  rw [← I.floorGenerator_val_eq_embedding_sourceY]
  exact hcompat _

end HereditaryAtomicity.DVRBase.BlockInput
