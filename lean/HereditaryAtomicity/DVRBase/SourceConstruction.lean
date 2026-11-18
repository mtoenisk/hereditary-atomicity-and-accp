import HereditaryAtomicity.DVRBase.SourceRings
import HereditaryAtomicity.DVRBase.BigMonomials
import HereditaryAtomicity.DVRBase.ModelOrders

/-!
# Literal source generators for the first-dead construction

The data below are the source-facing output of recursive block selection.
They retain actual elements of the source, exact endpoint equations, and
source divisibility witnesses. The construction of these data is separate.
-/

noncomputable section
namespace HereditaryAtomicity.DVRBase
open scoped NNReal BigOperators

variable {K : Type*} [Field K]

/-- The source block data include source elements, their exact chain equations and their
valuations. In the indexing used here ratio n corresponds to y_(n+1), and endpoint 0
is π^κ. -/
structure SourceBlockData (R : Subring K) where
  uniformizer : R
  uniformizer_ne_zero : uniformizer ≠ 0
  exponent : ℕ
  exponent_pos : 0 < exponent
  ratio : ℕ → R
  endpoint : ℕ → R
  endpoint_ne_zero : ∀ n, endpoint n ≠ 0
  top : endpoint 0 = uniformizer ^ exponent
  step : ∀ n, endpoint n = endpoint (n + 1) * ratio n
  valuation : Valuation K ℝ≥0
  normalized : realValuationOrder valuation (uniformizer : K) = 1
  ratio_order_pos : ∀ n, 0 < realValuationOrder valuation (ratio n : K)
  endpoint_order_ge_one : ∀ n, 1 ≤ realValuationOrder valuation (endpoint n : K)
  returnExponent : ℕ → ℕ
  returnExponent_pos : ∀ n, 0 < returnExponent n
  power_return : ∀ n, uniformizer ^ exponent ∣ ratio n ^ returnExponent n

namespace SourceBlockData
variable {R : Subring K} (D : SourceBlockData R)

def weight (n : ℕ) : ℝ := realValuationOrder D.valuation (D.ratio n : K)
def endpointOrder (n : ℕ) : ℝ := realValuationOrder D.valuation (D.endpoint n : K)
def threshold (n : ℕ) : ℝ :=
  2 * (D.exponent : ℝ) * ∑ i : Fin n, (D.returnExponent i.val : ℝ)

@[simp] theorem threshold_zero : D.threshold 0 = 0 := by simp [threshold]

theorem ratio_ne_zero (n : ℕ) : D.ratio n ≠ 0 := by
  intro h
  apply D.endpoint_ne_zero n
  rw [D.step n, h, mul_zero]

theorem endpointOrder_step (n : ℕ) :
    D.endpointOrder n = D.endpointOrder (n + 1) + D.weight n := by
  have h := congrArg R.subtype (D.step n)
  change (D.endpoint n : K) = (D.endpoint (n + 1) : K) * (D.ratio n : K) at h
  dsimp [endpointOrder, weight]
  rw [h, realValuationOrder_mul D.valuation
    (Subtype.coe_ne_coe.mpr (D.endpoint_ne_zero _))
    (Subtype.coe_ne_coe.mpr (D.ratio_ne_zero _))]

@[simp] theorem endpointOrder_zero : D.endpointOrder 0 = D.exponent := by
  dsimp [endpointOrder]
  rw [D.top]
  change realValuationOrder D.valuation ((D.uniformizer : K) ^ D.exponent) = _
  rw [realValuationOrder_pow, D.normalized, mul_one]

theorem endpointOrder_antitone : Antitone D.endpointOrder := by
  apply antitone_nat_of_succ_le
  intro n
  have h := D.endpointOrder_step n
  have hp := D.ratio_order_pos n
  change 0 < D.weight n at hp
  linarith

theorem weight_lt_exponent (n : ℕ) : D.weight n < D.exponent := by
  have hs := D.endpointOrder_step n
  have hb := D.endpointOrder_antitone (Nat.zero_le n)
  have he := D.endpoint_order_ge_one (n + 1)
  change 1 ≤ D.endpointOrder (n + 1) at he
  rw [D.endpointOrder_zero] at hb
  linarith

theorem endpointOrder_eq (n : ℕ) :
    D.endpointOrder n = D.exponent - ∑ i : Fin n, D.weight i.val := by
  induction n with
  | zero => simp
  | succ n ih =>
      have h := D.endpointOrder_step n
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last]
      linarith

/-- Agreement with the finite Laurent model at every admissible cut. -/
theorem endpointOrder_eq_remainingValue (n k : ℕ) (hk : k ≤ n) :
    D.endpointOrder k = remainingValue (fun i : Fin n => D.weight i.val) D.exponent k := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hkn : k < n := by omega
      have hs := D.endpointOrder_step k
      rw [remainingValue_succ _ _ hkn]
      have hp := ih (by omega)
      linarith

theorem threshold_succ (n : ℕ) :
    D.threshold (n + 1) = D.threshold n + 2 * D.exponent * D.returnExponent n := by
  simp only [threshold, Fin.sum_univ_castSucc, Fin.val_castSucc, Fin.val_last]
  ring

theorem threshold_ge_two_exponent {n : ℕ} (hn : 0 < n) :
    2 * (D.exponent : ℝ) ≤ D.threshold n := by
  have hi : (0 : ℕ) < n := hn
  have hsum : (1 : ℝ) ≤ ∑ i : Fin n, (D.returnExponent i.val : ℝ) := by
    have h1 : (1 : ℝ) ≤ D.returnExponent 0 := by exact_mod_cast D.returnExponent_pos 0
    exact h1.trans (Finset.single_le_sum (f := fun i : Fin n => (D.returnExponent i.val : ℝ)) (fun i _ => Nat.cast_nonneg _) (Finset.mem_univ (⟨0, hi⟩ : Fin n)))
  simpa only [mul_one, threshold] using mul_le_mul_of_nonneg_left hsum
    (show 0 ≤ 2 * (D.exponent : ℝ) by positivity)

/-- Source membership of each specified power-return quotient. -/
theorem power_return_mem (n : ℕ) :
    (D.ratio n : K) ^ D.returnExponent n / (D.uniformizer : K) ^ D.exponent ∈ R := by
  obtain ⟨a, ha⟩ := D.power_return n
  have h := congrArg R.subtype ha
  change (D.ratio n : K) ^ D.returnExponent n =
    (D.uniformizer : K) ^ D.exponent * (a : K) at h
  rw [h, mul_div_cancel_left₀ _
    (pow_ne_zero _ (Subtype.coe_ne_coe.mpr D.uniformizer_ne_zero))]
  exact a.property

/-- Deadness at a cut, using the same finite-coordinate convention as the model. -/
def DeadAt (e : ℕ) {n : ℕ} (μ : Fin n → ℕ) (k : ℕ) : Prop :=
  D.threshold k + remainingValue (fun i : Fin n => D.weight i.val) D.exponent k ≤
    partialValue (fun i : Fin n => D.weight i.val) e (fun i => (μ i : ℤ)) k

@[simp] theorem deadAt_zero (e : ℕ) {n : ℕ} (μ : Fin n → ℕ) :
    D.DeadAt e μ 0 ↔ D.exponent ≤ e := by
  simp [DeadAt]

/-- The coefficient exponent, exponent vector, and first threshold of a source generator. -/
structure FirstDead where
  length : ℕ
  length_pos : 0 < length
  coefficientExponent : ℕ
  powers : Fin length → ℕ
  dead : D.DeadAt coefficientExponent powers length
  earlier : ∀ k < length, ¬ D.DeadAt coefficientExponent powers k

namespace FirstDead
variable {D} (h : D.FirstDead)

def value : K :=
  (D.uniformizer : K) ^ h.coefficientExponent / (D.uniformizer : K) ^ D.exponent *
    ∏ i : Fin h.length, (D.ratio i.val : K) ^ (h.powers i + 1)

theorem coefficientExponent_lt : h.coefficientExponent < D.exponent := by
  have hn := h.earlier 0 h.length_pos
  rw [D.deadAt_zero] at hn
  omega

theorem large : D.threshold h.length ≤
    (h.coefficientExponent : ℝ) - D.exponent +
      ∑ i : Fin h.length, ((h.powers i + 1 : ℕ) : ℝ) * D.weight i.val := by
  have hd := h.dead
  simp only [DeadAt, remainingValue, partialValue, prefixSum_top, Int.cast_natCast] at hd
  simp only [Nat.cast_add, Nat.cast_one, add_mul, one_mul, Finset.sum_add_distrib]
  linarith

theorem mem_source : h.value ∈ R := by
  exact large_monomial_mem_source R D.uniformizer D.uniformizer_ne_zero
    (fun i : Fin h.length => D.ratio i.val) D.exponent h.coefficientExponent
    (fun i => D.returnExponent i.val) (fun i => h.powers i + 1)
    (fun i => D.weight i.val) (fun i => D.power_return_mem i.val)
    (fun i => (D.ratio_order_pos i.val).le) (fun i => (D.weight_lt_exponent i.val).le)
    h.large

theorem value_ne_zero : h.value ≠ 0 := by
  apply mul_ne_zero
  · exact div_ne_zero (pow_ne_zero _ (Subtype.coe_ne_coe.mpr D.uniformizer_ne_zero))
      (pow_ne_zero _ (Subtype.coe_ne_coe.mpr D.uniformizer_ne_zero))
  · exact Finset.prod_ne_zero_iff.mpr (fun i _ =>
      pow_ne_zero _ (Subtype.coe_ne_coe.mpr (D.ratio_ne_zero i.val)))

theorem value_order : realValuationOrder D.valuation h.value =
    (h.coefficientExponent : ℝ) - D.exponent +
      ∑ i : Fin h.length, ((h.powers i + 1 : ℕ) : ℝ) * D.weight i.val := by
  have hp : (D.uniformizer : K) ≠ 0 := Subtype.coe_ne_coe.mpr D.uniformizer_ne_zero
  have hy : ∀ i : Fin h.length, (D.ratio i.val : K) ^ (h.powers i + 1) ≠ 0 :=
    fun i => pow_ne_zero _ (Subtype.coe_ne_coe.mpr (D.ratio_ne_zero i.val))
  rw [value, realValuationOrder_mul D.valuation
    (div_ne_zero (pow_ne_zero _ hp) (pow_ne_zero _ hp))
    (Finset.prod_ne_zero_iff.mpr (fun i _ => hy i)),
    realValuationOrder_div D.valuation (pow_ne_zero _ hp) (pow_ne_zero _ hp),
    realValuationOrder_pow, realValuationOrder_pow, D.normalized]
  simp only [mul_one]
  congr 1
  rw [realValuationOrder_prod D.valuation Finset.univ _ (fun i _ => hy i)]
  simp only [realValuationOrder_pow, weight]

theorem threshold_le_value_order : D.threshold h.length ≤
    realValuationOrder D.valuation h.value := by rw [h.value_order]; exact h.large

end FirstDead

/-- The endpoint really is the original coefficient power divided by the
preceding source ratios. This is an equality of source elements. -/
theorem endpoint_mul_prod (n : ℕ) :
    D.endpoint n * ∏ i : Fin n, D.ratio i.val = D.uniformizer ^ D.exponent := by
  induction n with
  | zero => simpa using D.top
  | succ n ih =>
      rw [Fin.prod_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last]
      calc
        _ = (D.endpoint (n + 1) * D.ratio n) * ∏ i : Fin n, D.ratio i.val := by ring
        _ = _ := by rw [← D.step n, ih]

/-- Evaluation of the formal endpoint monomial gives the original endpoint. -/
theorem endpoint_eq_quotient (n : ℕ) :
    (D.endpoint n : K) = (D.uniformizer : K) ^ D.exponent /
      ∏ i : Fin n, (D.ratio i.val : K) := by
  apply (eq_div_iff (Finset.prod_ne_zero_iff.mpr
    (fun i _ => Subtype.coe_ne_coe.mpr (D.ratio_ne_zero i.val)))).mpr
  simpa only [map_mul, map_pow, map_prod, Subring.subtype_apply] using
    congrArg R.subtype (D.endpoint_mul_prod n)

/-- The first-dead quotient is exactly the original monomial divided by its
original chain endpoint, not merely an element with the same valuation. -/
theorem FirstDead.value_mul_endpoint (h : D.FirstDead) :
    h.value * (D.endpoint h.length : K) =
      (D.uniformizer : K) ^ h.coefficientExponent *
        ∏ i : Fin h.length, (D.ratio i.val : K) ^ h.powers i := by
  have hprod : (D.endpoint h.length : K) * ∏ i : Fin h.length, (D.ratio i.val : K) =
      (D.uniformizer : K) ^ D.exponent := by
    simpa only [map_mul, map_pow, map_prod, Subring.subtype_apply] using
      congrArg R.subtype (D.endpoint_mul_prod h.length)
  have hp : (D.uniformizer : K) ^ D.exponent ≠ 0 :=
    pow_ne_zero _ (Subtype.coe_ne_coe.mpr D.uniformizer_ne_zero)
  dsimp [FirstDead.value]
  simp only [pow_succ, Finset.prod_mul_distrib]
  calc
    _ = ((D.uniformizer : K) ^ h.coefficientExponent / (D.uniformizer : K) ^ D.exponent) *
        (∏ i : Fin h.length, (D.ratio i.val : K) ^ h.powers i) *
        ((D.endpoint h.length : K) * ∏ i : Fin h.length, (D.ratio i.val : K)) := by ring
    _ = _ := by rw [hprod]; field_simp

/-- The literal generator ring R_* in the ambient field. -/
def sourceRing (O : Subring K) : Subring K :=
  sourceGeneratorRing O (fun n => (D.endpoint n : K)) (fun n => (D.ratio n : K))
    (Set.range (fun h : D.FirstDead => h.value))

theorem sourceRing_le (O : Subring K) (hOR : O ≤ R) : D.sourceRing O ≤ R :=
  sourceGeneratorRing_le O R _ _ _ hOR (fun n => (D.endpoint n).property)
    (fun n => (D.ratio n).property) (by rintro x ⟨h, rfl⟩; exact h.mem_source)

theorem coefficient_le_sourceRing (O : Subring K) : O ≤ D.sourceRing O :=
  coefficient_le_generatedOver O _

theorem endpoint_mem_sourceRing (O : Subring K) (n : ℕ) :
    (D.endpoint n : K) ∈ D.sourceRing O := endpoint_mem_sourceGeneratorRing O _ _ _ n

theorem ratio_mem_sourceRing (O : Subring K) (n : ℕ) :
    (D.ratio n : K) ∈ D.sourceRing O := ratio_mem_sourceGeneratorRing O _ _ _ n

theorem firstDead_mem_sourceRing (O : Subring K) (h : D.FirstDead) :
    h.value ∈ D.sourceRing O := extra_subset_sourceGeneratorRing O _ _ _ ⟨h, rfl⟩

/-- Containment in the valuation ring follows generatorwise. The original
source ring itself need not be contained in the valuation ring. -/
theorem sourceRing_bounded (O : Subring K) (hO : ∀ a : O, D.valuation (a : K) ≤ 1)
    (r : D.sourceRing O) : D.valuation (r : K) ≤ 1 := by
  have hz : ∀ n, D.valuation (D.endpoint n : K) ≤ 1 := fun n =>
    (realValuationOrder_nonneg_iff D.valuation
      (Subtype.coe_ne_coe.mpr (D.endpoint_ne_zero n))).mp
      ((show (0 : ℝ) ≤ 1 by norm_num).trans (D.endpoint_order_ge_one n))
  have hy : ∀ n, D.valuation (D.ratio n : K) ≤ 1 := fun n =>
    (realValuationOrder_nonneg_iff D.valuation
      (Subtype.coe_ne_coe.mpr (D.ratio_ne_zero n))).mp (D.ratio_order_pos n).le
  have hρ : ∀ h : D.FirstDead, D.valuation h.value ≤ 1 := by
    intro h
    apply (realValuationOrder_nonneg_iff D.valuation h.value_ne_zero).mp
    have hT : 0 ≤ D.threshold h.length := by unfold threshold; positivity
    exact hT.trans h.threshold_le_value_order
  have hle : D.sourceRing O ≤ D.valuation.valuationSubring.toSubring :=
    sourceGeneratorRing_le O _ _ _ _ (fun a ha => hO ⟨a, ha⟩)
      hz hy (by rintro a ⟨h, rfl⟩; exact hρ h)
  exact hle r.property

/-- Source generators with all indices bounded by one finite stage. -/
def generatorsAt (n : ℕ) : Set K :=
  {x | ∃ i ≤ n, x = (D.endpoint i : K)} ∪
  {x | ∃ i < n, x = (D.ratio i : K)} ∪
  {x | ∃ h : D.FirstDead, h.length ≤ n ∧ x = h.value}

theorem generatorsAt_mono : Monotone D.generatorsAt := by
  intro n m hnm x hx
  rcases hx with ((⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩) | ⟨h, hh, rfl⟩)
  · exact Or.inl (Or.inl ⟨i, hi.trans hnm, rfl⟩)
  · exact Or.inl (Or.inr ⟨i, hi.trans_le hnm, rfl⟩)
  · exact Or.inr ⟨h, hh.trans hnm, rfl⟩

theorem sourceRing_eq_generatedOver_iUnion (O : Subring K) :
    D.sourceRing O = generatedOver O (⋃ n, D.generatorsAt n) := by
  unfold sourceRing sourceGeneratorRing
  apply congrArg (generatedOver O)
  ext x
  constructor
  · rintro ((⟨i, rfl⟩ | ⟨i, rfl⟩) | ⟨h, rfl⟩)
    · exact Set.mem_iUnion.mpr ⟨i, Or.inl (Or.inl ⟨i, le_rfl, rfl⟩)⟩
    · exact Set.mem_iUnion.mpr ⟨i + 1, Or.inl (Or.inr ⟨i, Nat.lt_succ_self i, rfl⟩)⟩
    · exact Set.mem_iUnion.mpr ⟨h.length, Or.inr ⟨h, le_rfl, rfl⟩⟩
  · intro hx
    obtain ⟨n, ((⟨i, _, rfl⟩ | ⟨i, _, rfl⟩) | ⟨h, _, rfl⟩)⟩ := Set.mem_iUnion.mp hx
    · exact Or.inl (Or.inl ⟨i, rfl⟩)
    · exact Or.inl (Or.inr ⟨i, rfl⟩)
    · exact Or.inr ⟨h, rfl⟩

theorem mem_sourceRing_iff_finite_stage (O : Subring K) (x : K) :
    x ∈ D.sourceRing O ↔ ∃ n, x ∈ generatedOver O (D.generatorsAt n) := by
  rw [D.sourceRing_eq_generatedOver_iUnion O]
  exact mem_generatedOver_iUnion_iff O D.generatorsAt D.generatorsAt_mono x

/-- The original endpoints, now regarded inside the literal generator ring. -/
def ringEndpoint (O : Subring K) (n : ℕ) : D.sourceRing O :=
  ⟨D.endpoint n, D.endpoint_mem_sourceRing O n⟩

/-- The original block ratios, inside the literal generator ring. -/
def ringRatio (O : Subring K) (n : ℕ) : D.sourceRing O :=
  ⟨D.ratio n, D.ratio_mem_sourceRing O n⟩

theorem ring_step (O : Subring K) (n : ℕ) :
    D.ringEndpoint O n = D.ringEndpoint O (n + 1) * D.ringRatio O n := by
  apply Subtype.ext
  exact congrArg R.subtype (D.step n)

/-- The literal ascending endpoint ideal of R_*. -/
def sourceIdeal (O : Subring K) : Ideal (D.sourceRing O) := chainIdeal (D.ringEndpoint O)

/-- The selected-ratio coefficient ring, as a subring of R_*. -/
def selectedBase (O : Subring K) (Λ : Set ℕ) : Subring (D.sourceRing O) :=
  generatedOver (O.comap (D.sourceRing O).subtype) {x | ∃ n ∈ Λ, x = D.ringRatio O n}

theorem selectedRatio_mem (O : Subring K) (Λ : Set ℕ) {n : ℕ} (hn : n ∈ Λ) :
    D.ringRatio O n ∈ D.selectedBase O Λ :=
  generators_subset_generatedOver _ _ ⟨n, hn, rfl⟩

/-- The actual B+J subring, before applying the injective ambient inclusion. -/
def sourceThickening (O : Subring K) (Λ : Set ℕ) : Subring (D.sourceRing O) :=
  idealThickening (D.selectedBase O Λ) (D.sourceIdeal O)

/-- The actual field subring S_*^Λ. -/
def sourceSubring (O : Subring K) (Λ : Set ℕ) : Subring K :=
  (D.sourceThickening O Λ).map (D.sourceRing O).subtype

theorem sourceSubring_le_sourceRing (O : Subring K) (Λ : Set ℕ) :
    D.sourceSubring O Λ ≤ D.sourceRing O := by
  rintro x ⟨x, _, rfl⟩
  exact x.property

theorem sourceSubring_le (O : Subring K) (hOR : O ≤ R) (Λ : Set ℕ) :
    D.sourceSubring O Λ ≤ R :=
  (D.sourceSubring_le_sourceRing O Λ).trans (D.sourceRing_le O hOR)

theorem coefficient_le_sourceSubring (O : Subring K) (Λ : Set ℕ) :
    O ≤ D.sourceSubring O Λ := by
  intro x hx
  let xR : D.sourceRing O := ⟨x, D.coefficient_le_sourceRing O hx⟩
  have hxB : xR ∈ D.selectedBase O Λ :=
    coefficient_le_generatedOver _ _ (show xR ∈ O.comap (D.sourceRing O).subtype from hx)
  exact ⟨xR, base_le_idealThickening _ _ hxB, rfl⟩

theorem endpoint_mem_sourceSubring (O : Subring K) (Λ : Set ℕ) (n : ℕ) :
    (D.endpoint n : K) ∈ D.sourceSubring O Λ :=
  ⟨D.ringEndpoint O n,
    ideal_subset_idealThickening _ _ (endpoint_mem_chainIdeal (D.ringEndpoint O) n), rfl⟩

theorem mem_sourceThickening_iff (O : Subring K) (Λ : Set ℕ) (x : D.sourceRing O) :
    x ∈ D.sourceThickening O Λ ↔
      ∃ b : D.sourceRing O, b ∈ D.selectedBase O Λ ∧ ∃ n : ℕ,
        ∃ q : D.sourceRing O, x = b + D.ringEndpoint O n * q :=
  mem_chainThickening_iff _ _ _ (D.ring_step O) x

/-- Every nonzero element of the literal chain ideal splits in the same B+J,
with both factors intrinsic nonunits. This is the source-side factorization assertion. -/
theorem exists_nonunit_factors (O : Subring K)
    (hO : ∀ a : O, D.valuation (a : K) ≤ 1) (Λ : Set ℕ)
    (hcofinal : ∀ N : ℕ, ∃ m, N ≤ m ∧ m ∈ Λ)
    (g : D.sourceThickening O Λ) (hg : (g : D.sourceRing O) ∈ D.sourceIdeal O)
    (hg0 : g ≠ 0) :
    ∃ b c : D.sourceThickening O Λ, ¬ IsUnit b ∧ ¬ IsUnit c ∧ g = b * c := by
  exact exists_nonunit_factors_in_chainThickening (D.selectedBase O Λ)
    (D.ringEndpoint O) (D.ringRatio O) (D.ring_step O) Λ hcofinal
    (fun _ hn => D.selectedRatio_mem O Λ hn)
    (D.sourceRing O).subtype Subtype.val_injective D.valuation (D.sourceRing_bounded O hO)
    (fun n => lt_of_lt_of_le zero_lt_one (D.endpoint_order_ge_one n))
    (fun n _ => D.ratio_order_pos n) g hg hg0

end SourceBlockData
end HereditaryAtomicity.DVRBase
