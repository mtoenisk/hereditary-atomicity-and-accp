import HereditaryAtomicity.DVRBase.BlockDegrees

noncomputable section
open scoped NNReal
namespace HereditaryAtomicity.DVRBase

variable {R L : Type*} [CommRing R] [Field L]

lemma sourceBlock_first_dvd (t : ℕ → R) (a n : ℕ) : t a ∣ sourceBlock t a n := by
  have h := Finset.dvd_prod_of_mem (fun i => t (a + i))
    (show 0 ∈ Finset.range (n + 1) by simp)
  simpa only [Nat.add_zero, sourceBlock] using h

lemma UniformizerChainData.sourceBlock_power_return {π : R} {t : ℕ → R}
    (C : UniformizerChainData π t) (a n e : ℕ) (he : π ^ C.exponent ∣ t a ^ e) :
    π ^ C.exponent ∣ sourceBlock t a n ^ e := by
  exact he.trans (pow_dvd_pow_of_dvd (sourceBlock_first_dvd t a n) e)

lemma UniformizerChainData.strictAnti_endpoint_order {π : R} {t : ℕ → R}
    (C : UniformizerChainData π t) (f : R →+* L) (hf : Function.Injective f)
    (v : Valuation L ℝ≥0) (ht : ∀ n, 0 < realValuationOrder v (f (t n))) :
    StrictAnti fun n => realValuationOrder v (f (C.endpoint n)) := by
  apply strictAnti_nat_of_succ_lt
  intro n
  rw [C.step n, map_mul, realValuationOrder_mul v
    ((map_ne_zero_iff f hf).mpr (C.endpoint_ne_zero (n + 1)))
    ((map_ne_zero_iff f hf).mpr (C.ratio_ne_zero n))]
  linarith [ht n]

variable [IsDomain R]

lemma UniformizerChainData.sourceBlock_first_order_le {π : R} {t : ℕ → R}
    (C : UniformizerChainData π t) (f : R →+* L) (hf : Function.Injective f)
    (v : Valuation L ℝ≥0) (ht : ∀ n, 0 < realValuationOrder v (f (t n)))
    (a n : ℕ) :
    realValuationOrder v (f (t a)) ≤ realValuationOrder v (f (sourceBlock t a n)) := by
  simpa only [sourceBlock_zero] using
    (C.strictMono_sourceBlock_order f hf v ht a).monotone (Nat.zero_le n)

omit [IsDomain R] in
lemma UniformizerChainData.sourceBlock_order_lt_exponent {π : R} {t : ℕ → R}
    (C : UniformizerChainData π t) (f : R →+* L) (hf : Function.Injective f)
    (v : Valuation L ℝ≥0)
    (hfloor : ∀ n, 1 ≤ realValuationOrder v (f (C.endpoint n)))
    (hπ : realValuationOrder v (f π) = 1)
    (ht : ∀ n, 0 < realValuationOrder v (f (t n))) (a n : ℕ) :
    realValuationOrder v (f (sourceBlock t a n)) < C.exponent := by
  have htop : realValuationOrder v (f (C.endpoint 0)) = C.exponent := by
    rw [C.top, map_pow, realValuationOrder_pow, hπ, mul_one]
  have hbound := (C.strictAnti_endpoint_order f hf v ht).antitone (Nat.zero_le a)
  rw [htop] at hbound
  have hend := hfloor (a + n + 1)
  rw [C.map_sourceBlock_eq_div f hf a n,
    realValuationOrder_div v ((map_ne_zero_iff f hf).mpr (C.endpoint_ne_zero a))
      ((map_ne_zero_iff f hf).mpr (C.endpoint_ne_zero (a + n + 1)))]
  linarith

end HereditaryAtomicity.DVRBase

namespace HereditaryAtomicity.DVRBase

open scoped BigOperators NNReal

theorem selectedBlockIndices_strictMono (a len : ℕ → ℕ)
    (ha : ∀ n, a (n + 1) = a n + len n + 1) : StrictMono a := by
  apply strictMono_nat_of_lt_succ
  intro n
  rw [ha n]
  omega

variable {R L : Type*} [CommRing R] [Field L]

theorem UniformizerChainData.selected_sourceBlock_step {π : R} {t : ℕ → R}
    (C : UniformizerChainData π t) (a len : ℕ → ℕ)
    (ha : ∀ n, a (n + 1) = a n + len n + 1) (n : ℕ) :
    C.endpoint (a n) = C.endpoint (a (n + 1)) * sourceBlock t (a n) (len n) := by
  rw [ha n]
  exact C.endpoint_eq_mul_sourceBlock (a n) (len n)

variable [IsDomain R]

theorem UniformizerChainData.selected_endpoint_order_step {π : R} {t : ℕ → R}
    (C : UniformizerChainData π t) (f : R →+* L) (hf : Function.Injective f)
    (v : Valuation L ℝ≥0) (a len : ℕ → ℕ)
    (ha : ∀ n, a (n + 1) = a n + len n + 1) (n : ℕ) :
    realValuationOrder v (f (C.endpoint (a n))) =
      realValuationOrder v (f (C.endpoint (a (n + 1)))) +
        realValuationOrder v (f (sourceBlock t (a n) (len n))) := by
  rw [C.selected_sourceBlock_step a len ha n, map_mul]
  exact realValuationOrder_mul v
    ((map_ne_zero_iff f hf).mpr (C.endpoint_ne_zero (a (n + 1))))
    ((map_ne_zero_iff f hf).mpr (C.sourceBlock_ne_zero (a n) (len n)))

/-- The endpoint order equals the original exponent minus all preceding
selected block orders. This is an exact finite telescoping identity. -/
theorem UniformizerChainData.selected_endpoint_order_eq_sub_sum
    {π : R} {t : ℕ → R} (C : UniformizerChainData π t)
    (f : R →+* L) (hf : Function.Injective f) (v : Valuation L ℝ≥0)
    (hπ : realValuationOrder v (f π) = 1) (a len : ℕ → ℕ)
    (ha0 : a 0 = 0) (ha : ∀ n, a (n + 1) = a n + len n + 1) (n : ℕ) :
    realValuationOrder v (f (C.endpoint (a n))) = (C.exponent : ℝ) -
      ∑ j ∈ Finset.range n, realValuationOrder v (f (sourceBlock t (a j) (len j))) := by
  induction n with
  | zero =>
      rw [ha0, C.top, map_pow, realValuationOrder_pow, hπ]
      simp
  | succ n ih =>
      have hstep := C.selected_endpoint_order_step f hf v a len ha n
      rw [Finset.sum_range_succ]
      linarith

omit [IsDomain R] in
theorem UniformizerChainData.one_le_selected_endpoint_order
    {π : R} {t : ℕ → R} (C : UniformizerChainData π t)
    (f : R →+* L) (v : Valuation L ℝ≥0)
    (hfloor : ∀ n, 1 ≤ realValuationOrder v (f (C.endpoint n)))
    (a : ℕ → ℕ) (n : ℕ) :
    1 ≤ realValuationOrder v (f (C.endpoint (a n))) := hfloor (a n)

/-- The first ratio remains a positive lower bound for a selected block,
and every block order stays strictly below the original exponent. -/
theorem UniformizerChainData.selected_block_order_bounds
    {π : R} {t : ℕ → R} (C : UniformizerChainData π t)
    (f : R →+* L) (hf : Function.Injective f) (v : Valuation L ℝ≥0)
    (hfloor : ∀ n, 1 ≤ realValuationOrder v (f (C.endpoint n)))
    (hπ : realValuationOrder v (f π) = 1)
    (ht : ∀ n, 0 < realValuationOrder v (f (t n))) (a len : ℕ → ℕ) (n : ℕ) :
    realValuationOrder v (f (t (a n))) ≤
        realValuationOrder v (f (sourceBlock t (a n) (len n))) ∧
      0 < realValuationOrder v (f (sourceBlock t (a n) (len n))) ∧
      realValuationOrder v (f (sourceBlock t (a n) (len n))) < C.exponent := by
  have hfirst := C.sourceBlock_first_order_le f hf v ht (a n) (len n)
  exact ⟨hfirst, (ht (a n)).trans_le hfirst,
    C.sourceBlock_order_lt_exponent f hf v hfloor hπ ht (a n) (len n)⟩

/-- A degree bound chosen using the fixed first ratio also holds with the
order of the subsequently chosen whole block. -/
theorem UniformizerChainData.sourceBlock_degree_mul_ge
    {π : R} {t : ℕ → R} (C : UniformizerChainData π t)
    (f : R →+* L) (hf : Function.Injective f) (v : Valuation L ℝ≥0)
    (ht : ∀ n, 0 < realValuationOrder v (f (t n)))
    (a n d : ℕ) {B : ℝ}
    (hchoice : B ≤ (d : ℝ) * realValuationOrder v (f (t a))) :
    B ≤ (d : ℝ) * realValuationOrder v (f (sourceBlock t a n)) :=
  hchoice.trans (mul_le_mul_of_nonneg_left
    (C.sourceBlock_first_order_le f hf v ht a n) (Nat.cast_nonneg d))

section Thresholds

variable (κ : ℝ) (e : ℕ → ℕ) (T : ℕ → ℝ)

/-- Closed form for the threshold recurrence in Construction B. -/
theorem blockThreshold_eq_sum (hzero : T 0 = 0)
    (hstep : ∀ n, T (n + 1) = T n + 2 * κ * e n) (n : ℕ) :
    T n = 2 * κ * ∑ j ∈ Finset.range n, (e j : ℝ) := by
  induction n with
  | zero => simp [hzero]
  | succ n ih => rw [hstep n, ih, Finset.sum_range_succ]; ring

/-- Every threshold is nonnegative. -/
theorem blockThreshold_nonneg (hκ : 0 ≤ κ) (hzero : T 0 = 0)
    (hstep : ∀ n, T (n + 1) = T n + 2 * κ * e n) (n : ℕ) :
    0 ≤ T n := by
  rw [blockThreshold_eq_sum κ e T hzero hstep]
  positivity

/-- Each positive return exponent increases the threshold by at least 2κ. -/
theorem blockThreshold_step_ge (hκ : 0 ≤ κ) (he : ∀ n, 0 < e n)
    (hstep : ∀ n, T (n + 1) = T n + 2 * κ * e n) (n : ℕ) :
    T n + 2 * κ ≤ T (n + 1) := by
  rw [hstep n]
  have hen : (1 : ℝ) ≤ e n := by exact_mod_cast (Nat.succ_le_iff.mpr (he n))
  have hmul : 2 * κ ≤ 2 * κ * e n := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hen (by positivity : 0 ≤ 2 * κ)
  linarith

/-- Positive κ and positive return exponents make all thresholds increase
strictly. -/
theorem blockThreshold_strictMono (hκ : 0 < κ) (he : ∀ n, 0 < e n)
    (hstep : ∀ n, T (n + 1) = T n + 2 * κ * e n) : StrictMono T := by
  apply strictMono_nat_of_lt_succ
  intro n
  have hge := blockThreshold_step_ge κ e T hκ.le he hstep n
  linarith

/-- Every noninitial threshold is at least 2κ. -/
theorem blockThreshold_succ_ge (hκ : 0 ≤ κ) (he : ∀ n, 0 < e n)
    (hzero : T 0 = 0)
    (hstep : ∀ n, T (n + 1) = T n + 2 * κ * e n) (n : ℕ) :
    2 * κ ≤ T (n + 1) := by
  have hnonneg := blockThreshold_nonneg κ e T hκ hzero hstep n
  have hge := blockThreshold_step_ge κ e T hκ he hstep n
  linarith

end Thresholds

end HereditaryAtomicity.DVRBase
