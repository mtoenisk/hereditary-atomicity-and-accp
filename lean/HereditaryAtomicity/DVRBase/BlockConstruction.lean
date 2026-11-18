import HereditaryAtomicity.DVRBase.BlockNumerics
import HereditaryAtomicity.DVRBase.MovingTower
import HereditaryAtomicity.DVRBase.ValuationNorm

/-!
# Recursive source-block construction over a completed DVR base

Starting with nonzero chain endpoints of order at least one, choose blocks recursively
as in semilocal Proposition 5.2. The preceding basis loss and the first ratio's return
exponent are fixed before choosing the next degree. Finite-prefix invariance
transports the selected bound to the moving basis of the resulting tower.

Canonical completion wrappers identify norm orders and valuation orders and
install the nontrivial completed base norm from a base element of value below
one. No algebraicity of the entire ambient completion is assumed.
-/

noncomputable section
open scoped NNReal
namespace HereditaryAtomicity.DVRBase

/-- Fixed source and valued-field input to the block recursion. -/
structure BlockInput (R k L : Type*) [CommRing R] [IsDomain R]
    [Field k] [Field L] [Algebra k L] (π : R) (t : ℕ → R) where
  chain : UniformizerChainData π t
  embedding : R →+* L
  embedding_injective : Function.Injective embedding
  valuation : Valuation L ℝ≥0
  coefficient_orders : ∀ a : k, a ≠ 0 → ∃ z : ℤ,
    realValuationOrder valuation (algebraMap k L a) = z
  source_algebraic : ∀ r : R, IsAlgebraic k (embedding r)
  endpoint_order_ge_one : ∀ n, 1 ≤ realValuationOrder valuation (embedding (chain.endpoint n))
  uniformizer_order : realValuationOrder valuation (embedding π) = 1
  ratio_positive : ∀ n, 0 < realValuationOrder valuation (embedding (t n))

/-- A finite-history state. Only its first `n` sequence entries will be used
at stage `n`; its future entries remain auxiliary. -/
structure BlockState (k L : Type*) [Field k] [Field L] [Algebra k L] where
  index : ℕ
  threshold : ℝ
  values : ℕ → Lˣ
  algebraic : ∀ n, IsAlgebraic k (values n : L)

variable {R k L : Type*} [CommRing R] [IsDomain R]
  [Field k] [Field L] [Algebra k L] {π : R} {t : ℕ → R}

namespace BlockInput

variable (I : BlockInput R k L π t)

/-- The actual source block as an ambient unit. -/
def blockUnit (a n : ℕ) : Lˣ := Units.mk0 (I.embedding (sourceBlock t a n))
  ((map_ne_zero_iff I.embedding I.embedding_injective).mpr (I.chain.sourceBlock_ne_zero a n))

@[simp] theorem blockUnit_val (a n : ℕ) :
    (I.blockUnit a n : L) = I.embedding (sourceBlock t a n) := rfl

variable (loss : ℕ → BlockState k L → ℝ)

/-- A successor choice remembers the return exponent fixed before the degree
choice, and the exact quantitative bound for the chosen block. -/
structure Choice (n : ℕ) (s : BlockState k L) where
  power : ℕ
  power_pos : 0 < power
  power_return : π ^ I.chain.exponent ∣ t s.index ^ power
  length : ℕ
  growth : 3 * (I.chain.exponent : ℝ) *
      (2 * (s.threshold + 2 * I.chain.exponent * power) + loss n s) ≤
    (Module.finrank (movingField k s.values n)
      (IntermediateField.adjoin (movingField k s.values n)
        {I.embedding (sourceBlock t s.index length)}) : ℝ) *
      realValuationOrder I.valuation (I.embedding (t s.index))

/-- The finite-stage choice exists with every bound fixed first. -/
theorem choice_nonempty (n : ℕ) (s : BlockState k L) : Nonempty (I.Choice loss n s) := by
  let : FiniteDimensional k (movingField k s.values n) :=
    movingField_finiteDimensional k s.values s.algebraic n
  obtain ⟨e, he, heq⟩ := I.chain.ratio_power s.index
  obtain ⟨m, hm⟩ := I.chain.exists_sourceBlock_degree_mul_ge k
    (movingField k s.values n) L I.embedding I.embedding_injective I.valuation
    I.coefficient_orders I.source_algebraic I.endpoint_order_ge_one I.ratio_positive
    s.index (3 * (I.chain.exponent : ℝ) *
      (2 * (s.threshold + 2 * I.chain.exponent * e) + loss n s))
  exact ⟨⟨e, he, heq, m, hm⟩⟩

/-- Classical choices are made from the preceding finite state. -/
def choose (n : ℕ) (s : BlockState k L) : I.Choice loss n s :=
  Classical.choice (I.choice_nonempty loss n s)

/-- One stage extends the original-source index by the chosen positive block
length and changes just the next entry of the auxiliary generator sequence. -/
def advance (n : ℕ) (s : BlockState k L) (q : I.Choice loss n s) : BlockState k L where
  index := s.index + q.length + 1
  threshold := s.threshold + 2 * I.chain.exponent * q.power
  values := Function.update s.values n (I.blockUnit s.index q.length)
  algebraic i := by
    by_cases h : i = n
    · subst i
      simpa only [Function.update_self, blockUnit_val] using
        I.source_algebraic (sourceBlock t s.index q.length)
    · simpa only [Function.update_of_ne h] using s.algebraic i

/-- Initial finite state, before any source ratios have been selected. -/
def initial : BlockState k L where
  index := 0
  threshold := 0
  values := fun _ => 1
  algebraic _ := by simpa using (isAlgebraic_one : IsAlgebraic k (1 : L))

/-- The finite-history recursion makes the stage-loss choice precede every
new field adjunction. -/
def state : ℕ → BlockState k L
  | 0 => initial (k := k) (L := L)
  | n + 1 => I.advance loss n (state n) (I.choose loss n (state n))

@[simp] theorem state_zero : I.state loss 0 = initial (k := k) (L := L) := rfl

@[simp] theorem state_succ (n : ℕ) :
    I.state loss (n + 1) = I.advance loss n (I.state loss n)
      (I.choose loss n (I.state loss n)) := rfl

def index (n : ℕ) : ℕ := (I.state loss n).index

def length (n : ℕ) : ℕ := (I.choose loss n (I.state loss n)).length

def returnExponent (n : ℕ) : ℕ := (I.choose loss n (I.state loss n)).power

def threshold (n : ℕ) : ℝ := (I.state loss n).threshold

def omega (n : ℕ) : ℝ := loss n (I.state loss n)

/-- The final sequence consists of the block selected at its own stage. -/
def generator (n : ℕ) : Lˣ := I.blockUnit (I.index loss n) (I.length loss n)

@[simp] theorem index_zero : I.index loss 0 = 0 := rfl

@[simp] theorem index_succ (n : ℕ) :
    I.index loss (n + 1) = I.index loss n + I.length loss n + 1 := rfl

@[simp] theorem threshold_zero : I.threshold loss 0 = 0 := rfl

@[simp] theorem threshold_succ (n : ℕ) : I.threshold loss (n + 1) =
    I.threshold loss n + 2 * I.chain.exponent * I.returnExponent loss n := rfl

theorem index_strictMono : StrictMono (I.index loss) := by
  apply strictMono_nat_of_lt_succ
  intro n
  rw [I.index_succ]
  omega

theorem returnExponent_pos (n : ℕ) : 0 < I.returnExponent loss n :=
  (I.choose loss n (I.state loss n)).power_pos

theorem returnExponent_spec (n : ℕ) :
    π ^ I.chain.exponent ∣ t (I.index loss n) ^ I.returnExponent loss n :=
  (I.choose loss n (I.state loss n)).power_return

theorem generator_algebraic (n : ℕ) : IsAlgebraic k (I.generator loss n : L) :=
  I.source_algebraic (sourceBlock t (I.index loss n) (I.length loss n))

/-- Every finite state agrees with the final sequence at all earlier indices. -/
theorem state_prefix (n : ℕ) : ∀ i < n, (I.state loss n).values i = I.generator loss i := by
  induction n with
  | zero => intro i hi; omega
  | succ n ih =>
      intro i hi
      by_cases h : i = n
      · subst i
        exact Function.update_self _ _ _
      · have hi' : i < n := by omega
        change Function.update (I.state loss n).values n (I.generator loss n) i = _
        rw [Function.update_of_ne h]
        exact ih i hi'

/-- The field used to choose the next block is the actual previous field of
the resulting infinite tower. -/
theorem field_eq_state (n : ℕ) :
    movingField k (I.generator loss) n = movingField k (I.state loss n).values n :=
  movingField_congr_prefix k (fun i hi => (I.state_prefix loss n i hi).symm)

/-- The already-chosen first-ratio weight gives the required bound on the
actual relative degree in the final tower. -/
theorem degree_mul_first_ratio_ge (n : ℕ) :
    3 * (I.chain.exponent : ℝ) *
      (2 * I.threshold loss (n + 1) + I.omega loss n) ≤
    (movingDegree k (I.generator loss) n : ℝ) *
      realValuationOrder I.valuation (I.embedding (t (I.index loss n))) := by
  have h := (I.choose loss n (I.state loss n)).growth
  have hdegree : movingDegree k (I.generator loss) n =
      Module.finrank (movingField k (I.state loss n).values n)
        (IntermediateField.adjoin (movingField k (I.state loss n).values n)
          {I.embedding (sourceBlock t (I.index loss n) (I.length loss n))}) := by
    dsimp only [movingDegree]
    rw [I.field_eq_state loss n]
    exact (IntermediateField.adjoin.finrank
      ((I.generator_algebraic loss n).tower_top
        (movingField k (I.state loss n).values n)).isIntegral).symm
  rw [hdegree]
  exact h

end BlockInput
end HereditaryAtomicity.DVRBase
namespace HereditaryAtomicity.DVRBase.BlockInput

open scoped BigOperators NNReal

variable {R k L : Type*} [CommRing R] [IsDomain R]
  [Field k] [Field L] [Algebra k L] {π : R} {t : ℕ → R}
  (I : BlockInput R k L π t) (loss : ℕ → BlockState k L → ℝ)

/-- The selected block is a literal source element. -/
def sourceY (n : ℕ) : R := sourceBlock t (I.index loss n) (I.length loss n)

/-- The selected endpoint is a literal endpoint of the original chain. -/
def sourceZ (n : ℕ) : R := I.chain.endpoint (I.index loss n)

def blockOrder (n : ℕ) : ℝ := realValuationOrder I.valuation (I.embedding (I.sourceY loss n))

def endpointOrder (n : ℕ) : ℝ :=
  realValuationOrder I.valuation (I.embedding (I.sourceZ loss n))

@[simp] theorem generator_val_eq_embedding_sourceY (n : ℕ) :
    (I.generator loss n : L) = I.embedding (I.sourceY loss n) := rfl

theorem sourceY_ne_zero (n : ℕ) : I.sourceY loss n ≠ 0 :=
  I.chain.sourceBlock_ne_zero (I.index loss n) (I.length loss n)

theorem sourceZ_ne_zero (n : ℕ) : I.sourceZ loss n ≠ 0 :=
  I.chain.endpoint_ne_zero (I.index loss n)

@[simp] theorem sourceZ_zero : I.sourceZ loss 0 = π ^ I.chain.exponent := by
  exact I.chain.top

theorem sourceZ_step (n : ℕ) :
    I.sourceZ loss n = I.sourceZ loss (n + 1) * I.sourceY loss n :=
  I.chain.selected_sourceBlock_step (I.index loss) (I.length loss) (I.index_succ loss) n

/-- Endpoint divisibility is retained only when separately supplied by a client. -/
theorem uniformizer_dvd_sourceZ (hdiv : ∀ n, π ∣ I.chain.endpoint n)
    (n : ℕ) : π ∣ I.sourceZ loss n := hdiv (I.index loss n)

/-- The previously chosen return exponent works for the selected whole
block inside the source ring. -/
theorem sourceY_power_return (n : ℕ) :
    π ^ I.chain.exponent ∣ I.sourceY loss n ^ I.returnExponent loss n :=
  I.chain.sourceBlock_power_return (I.index loss n) (I.length loss n)
    (I.returnExponent loss n) (I.returnExponent_spec loss n)

theorem sourceY_power_return_pos (n : ℕ) :
    0 < I.returnExponent loss n ∧
      π ^ I.chain.exponent ∣ I.sourceY loss n ^ I.returnExponent loss n :=
  ⟨I.returnExponent_pos loss n, I.sourceY_power_return loss n⟩

theorem endpointOrder_eq_exponent_sub_sum (n : ℕ) :
    I.endpointOrder loss n = (I.chain.exponent : ℝ) -
      ∑ j ∈ Finset.range n, I.blockOrder loss j := by
  exact I.chain.selected_endpoint_order_eq_sub_sum I.embedding I.embedding_injective
    I.valuation I.uniformizer_order (I.index loss) (I.length loss) (I.index_zero loss)
      (I.index_succ loss) n

theorem one_le_endpointOrder (n : ℕ) : 1 ≤ I.endpointOrder loss n :=
  I.endpoint_order_ge_one (I.index loss n)

theorem blockOrder_bounds (n : ℕ) :
    realValuationOrder I.valuation (I.embedding (t (I.index loss n))) ≤ I.blockOrder loss n ∧
      0 < I.blockOrder loss n ∧ I.blockOrder loss n < I.chain.exponent :=
  I.chain.selected_block_order_bounds I.embedding I.embedding_injective I.valuation
    I.endpoint_order_ge_one I.uniformizer_order I.ratio_positive
    (I.index loss) (I.length loss) n

theorem blockOrder_pos (n : ℕ) : 0 < I.blockOrder loss n :=
  (I.blockOrder_bounds loss n).2.1

theorem blockOrder_lt_exponent (n : ℕ) : I.blockOrder loss n < I.chain.exponent :=
  (I.blockOrder_bounds loss n).2.2

theorem threshold_eq_sum (n : ℕ) :
    I.threshold loss n = 2 * (I.chain.exponent : ℝ) *
      ∑ j ∈ Finset.range n, (I.returnExponent loss j : ℝ) :=
  blockThreshold_eq_sum I.chain.exponent (I.returnExponent loss) (I.threshold loss)
    (I.threshold_zero loss) (I.threshold_succ loss) n

theorem threshold_step_ge (n : ℕ) :
    I.threshold loss n + 2 * I.chain.exponent ≤ I.threshold loss (n + 1) :=
  blockThreshold_step_ge I.chain.exponent (I.returnExponent loss) (I.threshold loss)
    (Nat.cast_nonneg _) (I.returnExponent_pos loss) (I.threshold_succ loss) n

theorem threshold_strictMono : StrictMono (I.threshold loss) :=
  blockThreshold_strictMono I.chain.exponent (I.returnExponent loss) (I.threshold loss)
    (by exact_mod_cast I.chain.exponent_pos) (I.returnExponent_pos loss)
      (I.threshold_succ loss)

theorem threshold_succ_ge (n : ℕ) :
    2 * I.chain.exponent ≤ I.threshold loss (n + 1) :=
  blockThreshold_succ_ge I.chain.exponent (I.returnExponent loss) (I.threshold loss)
    (Nat.cast_nonneg _) (I.returnExponent_pos loss) (I.threshold_zero loss)
      (I.threshold_succ loss) n

/-- H3 for the actual relative degree and the actual selected block order.
The threshold and basis-loss bound were fixed before this block was chosen. -/
theorem degree_mul_blockOrder_ge (n : ℕ) :
    3 * (I.chain.exponent : ℝ) *
      (2 * I.threshold loss (n + 1) + I.omega loss n) ≤
        (movingDegree k (I.generator loss) n : ℝ) * I.blockOrder loss n :=
  I.chain.sourceBlock_degree_mul_ge I.embedding I.embedding_injective I.valuation
    I.ratio_positive (I.index loss n) (I.length loss n)
      (movingDegree k (I.generator loss) n) (I.degree_mul_first_ratio_ge loss n)

end HereditaryAtomicity.DVRBase.BlockInput

namespace HereditaryAtomicity.DVRBase

section SelectedLoss

variable {k L : Type*} [NontriviallyNormedField k] [CompleteSpace k]
  [NormedField L] [NormedAlgebra k L]

/-- The actual current moving basis constant is chosen before the next block.
The initial basis is assigned constant one. -/
def BlockState.basisConstant (n : ℕ) (s : BlockState k L) : ℝ :=
  if n = 0 then 1 else Classical.choose
    (exists_movingTowerBasis_norm_bound k s.values s.algebraic n)

theorem BlockState.one_le_basisConstant (n : ℕ) (s : BlockState k L) :
    1 ≤ s.basisConstant n := by
  unfold BlockState.basisConstant
  split_ifs with h
  · exact le_rfl
  · exact (Classical.choose_spec
      (exists_movingTowerBasis_norm_bound k s.values s.algebraic n)).1

theorem BlockState.basisConstant_spec (n : ℕ) (s : BlockState k L) :
    ∀ z : movingField k s.values n, ∀ i,
      ‖(movingTowerBasis k s.values s.algebraic n).repr z i •
        movingTowerBasis k s.values s.algebraic n i‖ ≤ s.basisConstant n * ‖z‖ := by
  unfold BlockState.basisConstant
  split_ifs with h
  · subst n
    exact movingTowerBasis_zero_norm_bound k s.values s.algebraic
  · exact (Classical.choose_spec
      (exists_movingTowerBasis_norm_bound k s.values s.algebraic n)).2

/-- An admissible additive loss of the actual basis chosen from the finite
history. No least-loss property is claimed or needed for the block choice. -/
def BlockState.basisLoss (n : ℕ) (s : BlockState k L) : ℝ :=
  Real.log (s.basisConstant n)

@[simp] theorem BlockState.basisConstant_zero (s : BlockState k L) :
    s.basisConstant 0 = 1 := by simp [BlockState.basisConstant]

@[simp] theorem BlockState.basisLoss_zero (s : BlockState k L) :
    s.basisLoss 0 = 0 := by simp [BlockState.basisLoss]

theorem BlockState.basisLoss_nonneg (n : ℕ) (s : BlockState k L) :
    0 ≤ s.basisLoss n := Real.log_nonneg (s.one_le_basisConstant n)


variable {R : Type*} [CommRing R] [IsDomain R] {π : R} {t : ℕ → R}
  (I : BlockInput R k L π t)

/-- The basis constant recorded by the actual block construction. -/
def BlockInput.selectedBasisConstant (n : ℕ) : ℝ :=
  (I.state BlockState.basisLoss n).basisConstant n

theorem BlockInput.one_le_selectedBasisConstant (n : ℕ) :
    1 ≤ I.selectedBasisConstant n :=
  (I.state BlockState.basisLoss n).one_le_basisConstant n

@[simp] theorem BlockInput.selectedBasisConstant_zero :
    I.selectedBasisConstant 0 = 1 :=
  (I.state BlockState.basisLoss 0).basisConstant_zero

@[simp] theorem BlockInput.omega_basisLoss_zero : I.omega BlockState.basisLoss 0 = 0 :=
  (I.state BlockState.basisLoss 0).basisLoss_zero

theorem BlockInput.omega_basisLoss_nonneg (n : ℕ) :
    0 ≤ I.omega BlockState.basisLoss n :=
  (I.state BlockState.basisLoss n).basisLoss_nonneg n

theorem BlockInput.omega_basisLoss_eq_log (n : ℕ) :
    I.omega BlockState.basisLoss n = Real.log (I.selectedBasisConstant n) := rfl

end SelectedLoss
end HereditaryAtomicity.DVRBase

namespace HereditaryAtomicity.DVRBase

variable {R k K : Type*} [CommRing R] [IsDomain R] [Field k] [Field K]
  [Algebra k K] {π : R} {t : ℕ → R}

/-- Construction B uses the actual completed base and ambient completion.
Only original source elements, rather than the whole completion, are algebraic. -/
def BlockInput.completed
    (I : BlockInput R k K π t) (v : Valuation k ℝ≥0)
    (hext : ∀ a : k, I.valuation (algebraMap k K a) = v a) :
    letI := valuationCompletionNormedAlgebra v I.valuation hext
    BlockInput R (ValuationNormCompletion v) (ValuationNormCompletion I.valuation) π t := by
  letI := valuationCompletionNormedAlgebra v I.valuation hext
  refine {
    chain := I.chain
    embedding := (algebraMap K (ValuationNormCompletion I.valuation)).comp I.embedding
    embedding_injective := (algebraMap K (ValuationNormCompletion I.valuation)).injective.comp
      I.embedding_injective
    valuation := completionValuation I.valuation
    coefficient_orders := ?_
    source_algebraic := ?_
    endpoint_order_ge_one := ?_
    uniformizer_order := ?_
    ratio_positive := ?_
  }
  · intro a ha
    have hc : ∀ b : k, b ≠ 0 → ∃ z : ℤ, realValuationOrder v b = z := by
      intro b hb
      obtain ⟨z, hz⟩ := I.coefficient_orders b hb
      exact ⟨z, by simpa only [realValuationOrder, hext b] using hz⟩
    obtain ⟨z, hz⟩ := completion_order_integral v hc a ha
    refine ⟨z, ?_⟩
    change -Real.log ((completionValuation I.valuation)
      (algebraMap (ValuationNormCompletion v) (ValuationNormCompletion I.valuation) a) : ℝ) = z
    rw [completionValuation_restrict v I.valuation hext a]
    exact hz
  · intro r
    exact isAlgebraic_completion_source v I.valuation hext (I.embedding r)
      (I.source_algebraic r)
  · intro n
    change 1 ≤ -Real.log ((completionValuation I.valuation)
      (algebraMap K (ValuationNormCompletion I.valuation)
        (I.embedding (I.chain.endpoint n))) : ℝ)
    simpa only [completionValuation_algebraMap, realValuationOrder] using I.endpoint_order_ge_one n
  · change -Real.log ((completionValuation I.valuation)
      (algebraMap K (ValuationNormCompletion I.valuation) (I.embedding π)) : ℝ) = 1
    simpa only [completionValuation_algebraMap, realValuationOrder] using I.uniformizer_order
  · intro n
    change 0 < -Real.log ((completionValuation I.valuation)
      (algebraMap K (ValuationNormCompletion I.valuation) (I.embedding (t n))) : ℝ)
    simpa only [completionValuation_algebraMap, realValuationOrder] using I.ratio_positive n

@[simp] theorem BlockInput.completed_embedding
    (I : BlockInput R k K π t) (v : Valuation k ℝ≥0)
    (hext : ∀ a : k, I.valuation (algebraMap k K a) = v a) (r : R) :
    letI := valuationCompletionNormedAlgebra v I.valuation hext
    (I.completed v hext).embedding r =
      algebraMap K (ValuationNormCompletion I.valuation) (I.embedding r) := rfl

/-- In the actual completion the additive valuation order and the norm order
used by the moving-basis estimates agree literally. -/
theorem BlockInput.completed_order_eq_neg_log_norm
    (I : BlockInput R k K π t) (v : Valuation k ℝ≥0)
    (hext : ∀ a : k, I.valuation (algebraMap k K a) = v a)
    (x : ValuationNormCompletion I.valuation) :
    letI := valuationCompletionNormedAlgebra v I.valuation hext
    realValuationOrder (I.completed v hext).valuation x = -Real.log ‖x‖ := rfl

end HereditaryAtomicity.DVRBase

namespace HereditaryAtomicity.DVRBase.BlockInput

variable {R k L : Type*} [CommRing R] [IsDomain R]
  [NontriviallyNormedField k] [CompleteSpace k] [NormedField L] [NormedAlgebra k L]
  {π : R} {t : ℕ → R} (I : BlockInput R k L π t)

/-- The bound selected from the preceding finite history is a bound for the
actual preceding basis of the resulting infinite tower. -/
theorem selectedBasisConstant_spec (n : ℕ) :
    ∀ z : movingField k (I.generator BlockState.basisLoss) n, ∀ i,
      ‖(movingTowerBasis k (I.generator BlockState.basisLoss)
        (I.generator_algebraic BlockState.basisLoss) n).repr z i •
          movingTowerBasis k (I.generator BlockState.basisLoss)
            (I.generator_algebraic BlockState.basisLoss) n i‖ ≤
      I.selectedBasisConstant n * ‖z‖ :=
  movingTowerBasis_norm_bound_congr_prefix k (I.state BlockState.basisLoss n).algebraic
    (I.generator_algebraic BlockState.basisLoss) (I.state_prefix BlockState.basisLoss n)
    ((I.state BlockState.basisLoss n).basisConstant_spec n)

/-- The basis bound for the actual preceding basis and the loss already used by the
recursive degree choice. -/
theorem selected_basis_order_bound (n : ℕ)
    (x : movingField k (I.generator BlockState.basisLoss) n) (hx : x ≠ 0)
    (β : WindowExponent
      (fun i : Fin n => movingDegree k (I.generator BlockState.basisLoss) i.val))
    (hβ : (movingTowerBasis k (I.generator BlockState.basisLoss)
      (I.generator_algebraic BlockState.basisLoss) n).repr x β ≠ 0) :
    -Real.log ‖x‖ - I.omega BlockState.basisLoss n ≤
      -Real.log ‖(movingTowerBasis k (I.generator BlockState.basisLoss)
        (I.generator_algebraic BlockState.basisLoss) n).repr x β •
          movingTowerBasis k (I.generator BlockState.basisLoss)
            (I.generator_algebraic BlockState.basisLoss) n β‖ := by
  have hC : 0 < I.selectedBasisConstant n :=
    lt_of_lt_of_le zero_lt_one (I.one_le_selectedBasisConstant n)
  have ht : 0 < ‖(movingTowerBasis k (I.generator BlockState.basisLoss)
      (I.generator_algebraic BlockState.basisLoss) n).repr x β •
        movingTowerBasis k (I.generator BlockState.basisLoss)
          (I.generator_algebraic BlockState.basisLoss) n β‖ :=
    norm_pos_iff.mpr (smul_ne_zero hβ ((movingTowerBasis k
      (I.generator BlockState.basisLoss) (I.generator_algebraic BlockState.basisLoss) n).ne_zero β))
  have hl := Real.log_le_log ht (I.selectedBasisConstant_spec n x β)
  rw [Real.log_mul hC.ne' (norm_ne_zero_iff.mpr hx)] at hl
  rw [I.omega_basisLoss_eq_log]
  linarith

variable [IsUltrametricDist L]

/-- The constructed blocks satisfy the monomial basis bound with exactly the earlier basis loss
used when their degree was selected. There is no coefficient-estimate premise. -/
theorem selected_monomial_order_bound (n : ℕ) (c : k) (α : Fin (n + 1) → ℤ)
    (β : WindowExponent
      (fun i : Fin (n + 1) => movingDegree k (I.generator BlockState.basisLoss) i.val))
    (hβ : (movingTowerBasis k (I.generator BlockState.basisLoss)
        (I.generator_algebraic BlockState.basisLoss) (n + 1)).repr
      (c • movingMonomial k (I.generator BlockState.basisLoss) (n + 1) α) β ≠ 0) :
    -Real.log ‖c • movingMonomial k (I.generator BlockState.basisLoss) (n + 1) α‖ -
        I.omega BlockState.basisLoss n ≤
      -Real.log ‖(movingTowerBasis k (I.generator BlockState.basisLoss)
          (I.generator_algebraic BlockState.basisLoss) (n + 1)).repr
        (c • movingMonomial k (I.generator BlockState.basisLoss) (n + 1) α) β •
          movingTowerBasis k (I.generator BlockState.basisLoss)
            (I.generator_algebraic BlockState.basisLoss) (n + 1) β‖ :=
  order_movingTowerBasis_monomial_term_ge k (I.generator BlockState.basisLoss)
    (I.generator_algebraic BlockState.basisLoss) n (I.one_le_selectedBasisConstant n)
    (I.selectedBasisConstant_spec n) c α β hβ

/-- The valuation form of the monomial basis bound, explicitly tied to the same norm used to
choose the recursive losses. The canonical completed input supplies `hcompat`
by `completed_order_eq_neg_log_norm`. -/
theorem selected_monomial_valuation_bound
    (hcompat : ∀ x : L, realValuationOrder I.valuation x = -Real.log ‖x‖)
    (n : ℕ) (c : k) (α : Fin (n + 1) → ℤ)
    (β : WindowExponent
      (fun i : Fin (n + 1) => movingDegree k (I.generator BlockState.basisLoss) i.val))
    (hβ : (movingTowerBasis k (I.generator BlockState.basisLoss)
        (I.generator_algebraic BlockState.basisLoss) (n + 1)).repr
      (c • movingMonomial k (I.generator BlockState.basisLoss) (n + 1) α) β ≠ 0) :
    realValuationOrder I.valuation
        ((c • movingMonomial k (I.generator BlockState.basisLoss) (n + 1) α :
          movingField k (I.generator BlockState.basisLoss) (n + 1)) : L) -
        I.omega BlockState.basisLoss n ≤
      realValuationOrder I.valuation
        (((movingTowerBasis k (I.generator BlockState.basisLoss)
            (I.generator_algebraic BlockState.basisLoss) (n + 1)).repr
          (c • movingMonomial k (I.generator BlockState.basisLoss) (n + 1) α) β •
            movingTowerBasis k (I.generator BlockState.basisLoss)
              (I.generator_algebraic BlockState.basisLoss) (n + 1) β :
                movingField k (I.generator BlockState.basisLoss) (n + 1)) : L) := by
  rw [hcompat, hcompat]
  exact I.selected_monomial_order_bound n c α β hβ

end HereditaryAtomicity.DVRBase.BlockInput

namespace HereditaryAtomicity.DVRBase.BlockInput

variable {R k K : Type*} [CommRing R] [IsDomain R] [Field k] [Field K]
  [Algebra k K] {π : R} {t : ℕ → R} (I : BlockInput R k K π t)
  (v : Valuation k ℝ≥0) (hext : ∀ a : k, I.valuation (algebraMap k K a) = v a)
  {p : k} (hp : p ≠ 0) (hvp : v p < 1)

/-- The actual completed-base block construction satisfies H3 with its own
previous-basis loss. A base element of value below one supplies the required
nontrivial norm; for the DVR application this is the base uniformizer. -/
theorem completed_degree_mul_blockOrder_ge :
    letI := valuationCompletionNormedAlgebra v I.valuation hext
    letI := valuationNormCompletion_nontriviallyNormedField v hp hvp
    let B := I.completed v hext
    ∀ n, 3 * (B.chain.exponent : ℝ) *
      (2 * B.threshold BlockState.basisLoss (n + 1) + B.omega BlockState.basisLoss n) ≤
        (movingDegree (ValuationNormCompletion v) (B.generator BlockState.basisLoss) n : ℝ) *
          B.blockOrder BlockState.basisLoss n := by
  let := valuationCompletionNormedAlgebra v I.valuation hext
  let := valuationNormCompletion_nontriviallyNormedField v hp hvp
  exact (I.completed v hext).degree_mul_blockOrder_ge BlockState.basisLoss

/-- The same actual construction has initial loss zero and nonnegative later
losses; these are selected from the completed finite moving bases. -/
theorem completed_omega_properties :
    letI := valuationCompletionNormedAlgebra v I.valuation hext
    letI := valuationNormCompletion_nontriviallyNormedField v hp hvp
    let B := I.completed v hext
    B.omega BlockState.basisLoss 0 = 0 ∧ ∀ n, 0 ≤ B.omega BlockState.basisLoss n := by
  let := valuationCompletionNormedAlgebra v I.valuation hext
  let := valuationNormCompletion_nontriviallyNormedField v hp hvp
  exact ⟨(I.completed v hext).omega_basisLoss_zero,
    (I.completed v hext).omega_basisLoss_nonneg⟩

end HereditaryAtomicity.DVRBase.BlockInput

namespace HereditaryAtomicity.DVRBase.BlockInput

variable {R k K : Type*} [CommRing R] [IsDomain R] [Field k] [Field K]
  [Algebra k K] {π : R} {t : ℕ → R} (I : BlockInput R k K π t)
  (v : Valuation k ℝ≥0) (hext : ∀ a : k, I.valuation (algebraMap k K a) = v a)
  {p : k} (hp : p ≠ 0) (hvp : v p < 1)

/-- The completed construction supplies the monomial basis bound for the very same valuation,
basis and earlier loss that occur in its degree-growth inequality. -/
theorem completed_monomial_valuation_bound :
    letI := valuationCompletionNormedAlgebra v I.valuation hext
    letI := valuationNormCompletion_nontriviallyNormedField v hp hvp
    let B := I.completed v hext
    ∀ n (c : ValuationNormCompletion v) (α : Fin (n + 1) → ℤ)
      (β : WindowExponent (fun i : Fin (n + 1) =>
        movingDegree (ValuationNormCompletion v) (B.generator BlockState.basisLoss) i.val)),
      let b := movingTowerBasis (ValuationNormCompletion v) (B.generator BlockState.basisLoss)
        (B.generator_algebraic BlockState.basisLoss) (n + 1)
      let x := c • movingMonomial (ValuationNormCompletion v)
        (B.generator BlockState.basisLoss) (n + 1) α
      b.repr x β ≠ 0 →
        realValuationOrder B.valuation (x : ValuationNormCompletion I.valuation) -
            B.omega BlockState.basisLoss n ≤
          realValuationOrder B.valuation
            ((b.repr x β • b β : movingField (ValuationNormCompletion v)
              (B.generator BlockState.basisLoss) (n + 1)) : ValuationNormCompletion I.valuation) := by
  let := valuationCompletionNormedAlgebra v I.valuation hext
  let := valuationNormCompletion_nontriviallyNormedField v hp hvp
  dsimp only
  intro n c α β hβ
  exact (I.completed v hext).selected_monomial_valuation_bound
    (I.completed_order_eq_neg_log_norm v hext) n c α β hβ

end HereditaryAtomicity.DVRBase.BlockInput
