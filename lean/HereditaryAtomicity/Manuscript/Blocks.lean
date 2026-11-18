import HereditaryAtomicity.Manuscript.Early
import HereditaryAtomicity.DVRBase.BlockFloor
import HereditaryAtomicity.DVRBase.BigMonomials

/-!
# Selecting blocks of a normalized chain

The block with Lean index `j` is the paper's block `j+1`. Endpoints and
thresholds start at zero in both conventions.
-/

noncomputable section
open scoped BigOperators NNReal
namespace HereditaryAtomicity.Manuscript
open DVRBase

variable {A k L : Type*} [CommRing A] [IsDomain A] [Field k] [Field L] [Algebra k L]
  {π : A} {t : ℕ → A}

-- Manuscript: lem:degreegrowth
/-- Relative degrees of quotients between the specified first endpoint and
the later endpoints exceed every proposed bound over every finite level. -/
theorem endpoint_quotient_degrees_unbounded (I : BlockInput A k L π t)
    (F : IntermediateField k L) [FiniteDimensional k F] (a M : ℕ) :
    ∃ b > a, M < Module.finrank F (IntermediateField.adjoin F
      {I.embedding (I.chain.endpoint a) / I.embedding (I.chain.endpoint b)}) := by
  obtain ⟨n, h⟩ := relative_adjoin_finrank_unbounded_of_strictMono_order k F L I.valuation
    I.coefficient_orders (fun n => I.embedding (sourceBlock t a n))
    (fun n => (map_ne_zero_iff _ I.embedding_injective).mpr (I.chain.sourceBlock_ne_zero a n))
    (fun n => I.source_algebraic _) (I.chain.strictMono_sourceBlock_order
      _ I.embedding_injective _ I.ratio_positive a) (I.chain.bddAbove_sourceBlock_order
      _ I.embedding_injective _ I.endpoint_order_ge_one a) M
  rw [I.chain.map_sourceBlock_eq_div _ I.embedding_injective a n] at h
  exact ⟨a + n + 1, by omega, h⟩

/-- Start indices and lengths of consecutive nonempty blocks. The length
parameter counts the factors following the block's first ratio. -/
structure BlockCuts where
  index : ℕ → ℕ
  length : ℕ → ℕ
  first : index 0 = 0
  next : ∀ j, index (j + 1) = index j + length j + 1

namespace BlockCuts

def ratio (b : BlockCuts) (t : ℕ → A) (j : ℕ) : A :=
  sourceBlock t (b.index j) (b.length j)

def generator (b : BlockCuts) (I : BlockInput A k L π t) (j : ℕ) : Lˣ :=
  I.blockUnit (b.index j) (b.length j)

def weight (b : BlockCuts) (I : BlockInput A k L π t) (j : ℕ) : ℝ :=
  realValuationOrder I.valuation (I.embedding (b.ratio t j))

/-- The exact threshold formed with the original chain's prescribed powers. -/
def threshold (b : BlockCuts) (κ : ℕ) (powers : ℕ → ℕ) (j : ℕ) : ℝ :=
  2 * (κ : ℝ) * ∑ i ∈ Finset.range j, (powers (b.index i) : ℝ)

end BlockCuts

/-- The block estimates, including the identities of the endpoints, the ratios,
the tower used for the relative degree, and the preceding prefix used for its loss. -/
structure BlockEstimates (I : BlockInput A k L π t) (powers : ℕ → ℕ)
    (loss : (n : ℕ) → (Fin n → Lˣ) → ℝ) (b : BlockCuts) : Prop where
  indices_increase : StrictMono b.index
  top : I.chain.endpoint (b.index 0) = π ^ I.chain.exponent
  quotient : ∀ j, I.embedding (b.ratio t j) =
    I.embedding (I.chain.endpoint (b.index j)) / I.embedding (I.chain.endpoint (b.index (j+1)))
  power_return : ∀ j, π ^ I.chain.exponent ∣ b.ratio t j ^ powers (b.index j)
  endpoint_order : ∀ j, realValuationOrder I.valuation (I.embedding (I.chain.endpoint (b.index j))) =
    (I.chain.exponent : ℝ) - ∑ i ∈ Finset.range j, b.weight I i
  endpoint_lower : ∀ j, 1 ≤ realValuationOrder I.valuation (I.embedding (I.chain.endpoint (b.index j)))
  weight_bounds : ∀ j, 0 < b.weight I j ∧ b.weight I j < I.chain.exponent
  initial_threshold : b.threshold I.chain.exponent powers 0 = 0
  next_threshold : ∀ j, b.threshold I.chain.exponent powers (j+1) =
    b.threshold I.chain.exponent powers j + 2 * I.chain.exponent * powers (b.index j)
  threshold_growth : ∀ j, b.threshold I.chain.exponent powers j + 2 * I.chain.exponent ≤
    b.threshold I.chain.exponent powers (j+1)
  degree_growth : ∀ j, 3 * (I.chain.exponent : ℝ) *
    (2 * b.threshold I.chain.exponent powers (j+1) + loss j (fun i => b.generator I i)) ≤
    (movingDegree k (b.generator I) j : ℝ) * b.weight I j

/-- The blocks can meet any loss fixed by their preceding finite prefix, using
the exponents supplied with the original chain in the threshold recurrence. -/
theorem exists_blocks_for_prefix_losses (I : BlockInput A k L π t)
    (powers : ℕ → ℕ) (hpos : ∀ j, 0 < powers j)
    (hreturn : ∀ j, π ^ I.chain.exponent ∣ t j ^ powers j)
    (loss : (n : ℕ) → (Fin n → Lˣ) → ℝ) :
    ∃ b : BlockCuts, BlockEstimates I powers loss b := by
  let stageLoss (n : ℕ) (s : BlockState k L) := loss n (fun i => s.values i)
  let floor (_ : ℕ) (s : BlockState k L) := powers s.index
  let b : BlockCuts := ⟨I.floorIndex stageLoss floor, I.floorLength stageLoss floor,
    I.floorIndex_zero stageLoss floor, I.floorIndex_succ stageLoss floor⟩
  have hstep (j : ℕ) : b.threshold I.chain.exponent powers (j+1) =
      b.threshold I.chain.exponent powers j + 2 * I.chain.exponent * powers (b.index j) := by
    simp only [BlockCuts.threshold, Finset.sum_range_succ, mul_add]
  have hbound (j : ℕ) : b.threshold I.chain.exponent powers j ≤ I.floorThreshold stageLoss floor j := by
    rw [I.floorThreshold_eq_sum]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Finset.sum_le_sum
    intro i _
    exact_mod_cast I.floorReturnExponent_ge stageLoss floor i
  refine ⟨b, I.floorIndex_strictMono stageLoss floor, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hstep, ?_, ?_⟩
  · rw [b.first, I.chain.top]
  · intro j
    rw [b.next j]
    exact I.chain.map_sourceBlock_eq_div _ I.embedding_injective _ _
  · intro j
    exact I.chain.sourceBlock_power_return _ _ _ (hreturn _)
  · exact I.floorEndpointOrder_eq_exponent_sub_sum stageLoss floor
  · exact I.floorOne_le_endpointOrder stageLoss floor
  · exact fun j => (I.floorBlockOrder_bounds stageLoss floor j).2
  · simp [BlockCuts.threshold]
  · intro j
    rw [hstep]
    have hm : (1 : ℝ) ≤ powers (b.index j) := by exact_mod_cast hpos (b.index j)
    nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) I.chain.exponent) (sub_nonneg.mpr hm)]
  · intro j
    have hprefix : (fun i : Fin j => (I.floorState stageLoss floor j).values i) =
        (fun i : Fin j => b.generator I i) := by
      funext i
      exact I.floorState_prefix stageLoss floor j i i.isLt
    have hΩ : I.floorOmega stageLoss floor j = loss j (fun i => b.generator I i) :=
      congrArg (loss j) hprefix
    have hdegree := I.floorDegree_mul_blockOrder_ge stageLoss floor j
    rw [hΩ] at hdegree
    exact le_trans (mul_le_mul_of_nonneg_left
      (add_le_add (mul_le_mul_of_nonneg_left (hbound (j+1)) (show (0 : ℝ) ≤ 2 by norm_num)) (le_refl _))
      (by positivity)) hdegree

-- Manuscript: prop:B
/-- Proposition 5.2 with the very same loss function as Lemma 4.5. The
degrees are calculated in the field tower generated by the selected blocks. -/
theorem exists_selected_blocks {K E : Type*} [NontriviallyNormedField K] [CompleteSpace K]
    [NormedField E] [NormedAlgebra K E] (I : BlockInput A K E π t)
    (powers : ℕ → ℕ) (hpos : ∀ j, 0 < powers j)
    (hreturn : ∀ j, π ^ I.chain.exponent ∣ t j ^ powers j) :
    ∃ b : BlockCuts, BlockEstimates I powers (windowLoss K) b :=
  exists_blocks_for_prefix_losses I powers hpos hreturn (windowLoss K)

-- Manuscript: lem:D
/-- A selected Laurent monomial of order at least the exact threshold is the
image of an element of the source ring. -/
theorem large_block_monomial_mem_source (I : BlockInput A k L π t)
    {powers : ℕ → ℕ} {loss : (n : ℕ) → (Fin n → Lˣ) → ℝ} {b : BlockCuts}
    (H : BlockEstimates I powers loss b) (l e : ℕ) (q : Fin l → ℕ)
    (hlarge : b.threshold I.chain.exponent powers l ≤ realValuationOrder I.valuation
      (I.embedding π ^ e / I.embedding π ^ I.chain.exponent *
        ∏ i : Fin l, I.embedding (b.ratio t i) ^ q i)) :
    I.embedding π ^ e / I.embedding π ^ I.chain.exponent *
      ∏ i : Fin l, I.embedding (b.ratio t i) ^ q i ∈ I.embedding.range := by
  have hp : I.embedding π ≠ 0 := by
    intro hz
    have h := I.uniformizer_order
    rw [hz, realValuationOrder_zero] at h
    norm_num at h
  have hy (i : Fin l) : I.embedding (b.ratio t i) ^ q i ≠ 0 :=
    pow_ne_zero _ ((map_ne_zero_iff _ I.embedding_injective).mpr (I.chain.sourceBlock_ne_zero _ _))
  rw [realValuationOrder_mul _ (div_ne_zero (pow_ne_zero _ hp) (pow_ne_zero _ hp))
    (Finset.prod_ne_zero_iff.mpr fun i _ => hy i),
    realValuationOrder_div _ (pow_ne_zero _ hp) (pow_ne_zero _ hp),
    realValuationOrder_prod _ Finset.univ _ (fun i _ => hy i)] at hlarge
  simp only [realValuationOrder_pow, I.uniformizer_order, mul_one] at hlarge
  have hd := large_monomial_numerator_dvd π (fun i : Fin l => b.ratio t i)
    I.chain.exponent e (fun i => powers (b.index i)) q (fun i => b.weight I i)
    (fun i => H.power_return i) (fun i => (H.weight_bounds i).1.le)
    (fun i => (H.weight_bounds i).2.le)
    (by
      rw [Fin.sum_univ_eq_sum_range (fun i => (powers (b.index i) : ℝ))]
      exact hlarge)
  obtain ⟨z, hz⟩ := hd
  refine ⟨z, ?_⟩
  have h := congrArg I.embedding hz
  simp only [map_mul, map_pow, map_prod] at h
  rw [div_mul_eq_mul_div, h, mul_div_cancel_left₀ _ (pow_ne_zero _ hp)]

end HereditaryAtomicity.Manuscript
