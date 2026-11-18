import HereditaryAtomicity.DVRBase.SourceModel
import HereditaryAtomicity.ArithmeticCoefficients
import HereditaryAtomicity.SparseProductCut

/-! Domination of a polynomial monomial in the source endpoint ideal. -/
noncomputable section
namespace HereditaryAtomicity.DVRBase
open scoped BigOperators NNReal

section Coefficients
variable {K : Type*} [Field K]

/-- An actual coefficient-ring unit has additive order zero at every
valuation containing that coefficient ring. -/
theorem coefficient_unit_order (O : Subring K) (v : Valuation K ℝ≥0)
    (hO : ∀ a : O, v (a : K) ≤ 1) (u : Oˣ) :
    realValuationOrder v ((u : O) : K) = 0 := by
  have hu : v ((u : O) : K) = 1 := coefficient_unit_value O.subtype v hO u.isUnit
  simp only [realValuationOrder, hu, NNReal.coe_one, Real.log_one, neg_zero]

/-- Exact uniformizer-power factorization of a nonzero element of an
embedded DVR, with the same equality retained in the ambient field. -/
theorem exists_dvr_coefficient_power (O : Subring K) [IsDiscreteValuationRing O]
    (π : O) (hπ : Irreducible π) (c : O) (hc : c ≠ 0) :
    ∃ (e : ℕ) (u : Oˣ), c = (u : O) * π ^ e ∧
      (c : K) = ((u : O) : K) * (π : K) ^ e := by
  obtain ⟨e, u, heq⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hc hπ
  refine ⟨e, u, heq, ?_⟩
  exact congrArg O.subtype heq

/-- The exact coefficient factorization and quotient unit, with the natural
exponent proved equal to the coefficient's normalized valuation order. -/
theorem exists_normalized_dvr_coefficient_power
    (O : Subring K) [IsDiscreteValuationRing O]
    (π : O) (hπ : Irreducible π) (v : Valuation K ℝ≥0)
    (hO : ∀ a : O, v (a : K) ≤ 1)
    (hnorm : realValuationOrder v (π : K) = 1) (c : O) (hc : c ≠ 0) :
    ∃ (e : ℕ) (u : Oˣ),
      (c : K) = ((u : O) : K) * (π : K) ^ e ∧
      (c : K) / (π : K) ^ e = ((u : O) : K) ∧
      realValuationOrder v (c : K) = e ∧
      realValuationOrder v ((u : O) : K) = 0 := by
  obtain ⟨e, u, _, heq⟩ := exists_dvr_coefficient_power O π hπ c hc
  have hp : (π : K) ≠ 0 := Subtype.coe_ne_coe.mpr hπ.ne_zero
  have hu : ((u : O) : K) ≠ 0 := Subtype.coe_ne_coe.mpr u.ne_zero
  have huord := coefficient_unit_order O v hO u
  refine ⟨e, u, heq, ?_, ?_, huord⟩
  · rw [heq, mul_div_cancel_right₀ _ (pow_ne_zero e hp)]
  · rw [heq, realValuationOrder_mul v hu (pow_ne_zero e hp),
      realValuationOrder_pow, huord, hnorm]
    simp

end Coefficients

/-- Restricting to a longer prefix does not change an earlier partial sum. -/
theorem prefixSum_castLE {n m : ℕ} (hm : m ≤ n) (f : Fin n → ℝ)
    (k : ℕ) (hk : k ≤ m) :
    prefixSum (fun i : Fin m => f (Fin.castLE hm i)) k = prefixSum f k := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [prefixSum_succ _ (by omega), prefixSum_succ _ (by omega), ih (by omega)]
      rfl


/-- An initial-coordinate product divides the full product in the same ring. -/
theorem fin_prefix_prod_dvd {A : Type*} [CommMonoid A] {n m : ℕ}
    (hm : m ≤ n) (f : Fin n → A) :
    (∏ i : Fin m, f (Fin.castLE hm i)) ∣ ∏ i : Fin n, f i := by
  classical
  have heq : (∏ i : Fin m, f (Fin.castLE hm i)) =
      ∏ i ∈ Finset.univ.image (Fin.castLE hm), f i := by
    rw [Finset.prod_image]
    intro a _ b _ hab
    exact Fin.castLE_injective hm hab
  rw [heq]
  exact Finset.prod_dvd_prod_of_subset _ _ f (Finset.subset_univ _)

/-- The actual coefficient inclusion in the source generator ring. -/
def SourceBlockData.coefficientToSource {K : Type*} [Field K] {R : Subring K}
    (D : SourceBlockData R) (O : Subring K) : O →+* D.sourceRing O :=
  Subring.inclusion (D.coefficient_le_sourceRing O)

namespace SourceBlockData
variable {K : Type*} [Field K] {R : Subring K} (D : SourceBlockData R)

/-- A polynomial term evaluated literally in the original source generator ring. -/
def sourcePolynomialTerm (O : Subring K) {n : ℕ} (c : O) (μ : Fin n → ℕ) :
    D.sourceRing O := D.coefficientToSource O c * ∏ i, D.ringRatio O i.val ^ μ i

@[simp] theorem sourcePolynomialTerm_coe (O : Subring K) {n : ℕ}
    (c : O) (μ : Fin n → ℕ) :
    (D.sourcePolynomialTerm O c μ : K) = (c : K) * ∏ i, (D.ratio i.val : K) ^ μ i := by
  simp [sourcePolynomialTerm, coefficientToSource, ringRatio]

/-- Deadness of a polynomial term depends only on its prefix at the tested cut. -/
theorem deadAt_castLE {n m : ℕ} (hm : m ≤ n) (e : ℕ) (μ : Fin n → ℕ)
    (k : ℕ) (hk : k ≤ m) :
    D.DeadAt e (fun i : Fin m => μ (Fin.castLE hm i)) k ↔ D.DeadAt e μ k := by
  dsimp only [DeadAt, remainingValue, partialValue]
  have hw := prefixSum_castLE hm (fun i => D.weight i.val) k hk
  have hp := prefixSum_castLE hm (fun i => ((μ i : ℤ) : ℝ) * D.weight i.val) k hk
  simp only [Fin.val_castLE] at hw hp
  rw [hw, hp]

/-- The least dead cut supplies an actual first-dead source generator unless
coefficient divisibility already makes the initial cut dead. -/
theorem exists_firstDead_prefix {n : ℕ} (e : ℕ) (μ : Fin n → ℕ)
    (hd : ∃ k, k ≤ n ∧ D.DeadAt e μ k) :
    D.exponent ≤ e ∨ ∃ h : D.FirstDead, ∃ hn : h.length ≤ n,
      h.coefficientExponent = e ∧ ∀ i, h.powers i = μ (Fin.castLE hn i) := by
  classical
  let l := Nat.find hd
  have hln : l ≤ n := (Nat.find_spec hd).1
  have hld : D.DeadAt e μ l := (Nat.find_spec hd).2
  by_cases hl : l = 0
  · left
    exact (D.deadAt_zero e μ).mp (hl ▸ hld)
  · right
    have hlpos : 0 < l := Nat.pos_of_ne_zero hl
    let h : D.FirstDead := {
      length := l
      length_pos := hlpos
      coefficientExponent := e
      powers := fun i => μ (Fin.castLE hln i)
      dead := (D.deadAt_castLE hln e μ l le_rfl).mpr hld
      earlier := by
        intro k hk hdead
        have hd' := (D.deadAt_castLE hln e μ k hk.le).mp hdead
        exact (Nat.not_le_of_lt hk) (Nat.find_min' hd ⟨hk.le.trans hln, hd'⟩)
    }
    exact ⟨h, hln, rfl, fun _ => rfl⟩

/-- A dead uniformizer-power polynomial monomial lies in the actual ascending
endpoint ideal, by a literal source factorization at its least dead cut. -/
theorem uniformizerPowerTerm_mem_sourceIdeal (O : Subring K) (π : O)
    (hπ : (π : K) = (D.uniformizer : K)) {n : ℕ} (e : ℕ) (μ : Fin n → ℕ)
    (hd : ∃ k, k ≤ n ∧ D.DeadAt e μ k) :
    D.sourcePolynomialTerm O (π ^ e) μ ∈ D.sourceIdeal O := by
  classical
  rcases D.exists_firstDead_prefix e μ hd with he | ⟨h, hn, he, hμ⟩
  · have htop : (D.coefficientToSource O π) ^ D.exponent = D.ringEndpoint O 0 := by
      apply Subtype.ext
      change (π : K) ^ D.exponent = (D.endpoint 0 : K)
      rw [D.top]
      exact congrArg (fun x : K => x ^ D.exponent) hπ
    have hmem : (D.coefficientToSource O π) ^ D.exponent ∈ D.sourceIdeal O := by
      rw [htop]
      exact endpoint_mem_chainIdeal _ 0
    obtain ⟨q, hq⟩ := pow_dvd_pow (D.coefficientToSource O π) he
    have hpow : (D.coefficientToSource O π) ^ e ∈ D.sourceIdeal O := by
      rw [hq]
      exact (D.sourceIdeal O).mul_mem_right q hmem
    simpa only [sourcePolynomialTerm, map_pow] using
      (D.sourceIdeal O).mul_mem_right (∏ i, D.ringRatio O i.val ^ μ i) hpow
  · let ρ : D.sourceRing O := ⟨h.value, D.firstDead_mem_sourceRing O h⟩
    have hprefix : D.coefficientToSource O (π ^ e) *
        (∏ i : Fin h.length, D.ringRatio O i.val ^ μ (Fin.castLE hn i)) =
        D.ringEndpoint O h.length * ρ := by
      apply Subtype.ext
      change (D.sourcePolynomialTerm O (π ^ e)
        (fun i : Fin h.length => μ (Fin.castLE hn i)) : K) = _
      rw [D.sourcePolynomialTerm_coe]
      change (π : K) ^ e * (∏ i : Fin h.length,
        (D.ratio i.val : K) ^ μ (Fin.castLE hn i)) = (D.endpoint h.length : K) * h.value
      rw [mul_comm _ h.value, h.value_mul_endpoint, he, hπ]
      congr 1
      exact Finset.prod_congr rfl (fun i _ => congrArg _ (hμ i).symm)
    have hm : D.coefficientToSource O (π ^ e) *
        (∏ i : Fin h.length, D.ringRatio O i.val ^ μ (Fin.castLE hn i)) ∈
        D.sourceIdeal O := by
      rw [hprefix]
      exact (D.sourceIdeal O).mul_mem_right ρ (endpoint_mem_chainIdeal _ h.length)
    obtain ⟨q, hq⟩ := fin_prefix_prod_dvd hn (fun i : Fin n => D.ringRatio O i.val ^ μ i)
    have hfull : D.sourcePolynomialTerm O (π ^ e) μ =
        (D.coefficientToSource O (π ^ e) *
          ∏ i : Fin h.length, D.ringRatio O i.val ^ μ (Fin.castLE hn i)) * q := by
      dsimp only [sourcePolynomialTerm]
      rw [hq]
      simp only [Fin.val_castLE, mul_assoc]
    rw [hfull]
    exact (D.sourceIdeal O).mul_mem_right q hm

/-- Domination for one original DVR coefficient and a polynomial exponent.
The actual unit factor remains in the coefficient DVR, including order zero. -/
theorem sourcePolynomialTerm_mem_sourceIdeal_of_dead
    (O : Subring K) [IsDiscreteValuationRing O] (π : O) (hπirr : Irreducible π)
    (hπ : (π : K) = (D.uniformizer : K))
    (hO : ∀ c : O, D.valuation (c : K) ≤ 1)
    {n : ℕ} (c : O) (μ : Fin n → ℕ)
    (hd : c ≠ 0 → ∃ k, k ≤ n ∧
      D.threshold k + remainingValue (fun i : Fin n => D.weight i.val) D.exponent k ≤
        partialValue (fun i : Fin n => D.weight i.val)
          (realValuationOrder D.valuation (c : K)) (fun i => (μ i : ℤ)) k) :
    D.sourcePolynomialTerm O c μ ∈ D.sourceIdeal O := by
  by_cases hc : c = 0
  · simp [sourcePolynomialTerm, hc]
  · have hnorm : realValuationOrder D.valuation (π : K) = 1 := hπ ▸ D.normalized
    obtain ⟨e, u, heq, _, hord, _⟩ :=
      exists_normalized_dvr_coefficient_power O π hπirr D.valuation hO hnorm c hc
    have hcoeff : c = (u : O) * π ^ e := Subtype.ext heq
    have hdead : ∃ k, k ≤ n ∧ D.DeadAt e μ k := by
      simpa only [hord, DeadAt] using hd hc
    have hmem := D.uniformizerPowerTerm_mem_sourceIdeal O π hπ e μ hdead
    have hterm : D.sourcePolynomialTerm O c μ =
        D.coefficientToSource O (u : O) * D.sourcePolynomialTerm O (π ^ e) μ := by
      simp only [sourcePolynomialTerm, hcoeff, map_mul, mul_assoc]
    rw [hterm]
    exact (D.sourceIdeal O).mul_mem_left _ hmem

/-- A finite Laurent polynomial with original DVR coefficients and nonnegative
exponents evaluates into the source ideal when all its nonzero terms are dead. -/
theorem exists_sourceIdeal_evaluation_of_dead_terms
    (O : Subring K) [IsDiscreteValuationRing O] (π : O) (hπirr : Irreducible π)
    (hπ : (π : K) = (D.uniformizer : K))
    (hO : ∀ c : O, D.valuation (c : K) ≤ 1)
    {n : ℕ} (f : Laurent (FractionRing O) n)
    (hcoeff : ∀ β, f.coeff β ≠ 0 → ∃ c : O, algebraMap O (FractionRing O) c = f.coeff β)
    (hnonneg : ∀ β, f.coeff β ≠ 0 → ∀ i, 0 ≤ β i)
    (hdead : ∀ β, f.coeff β ≠ 0 → ∃ k, k ≤ n ∧
      D.threshold k + remainingValue (fun i : Fin n => D.weight i.val) D.exponent k ≤
        partialValue (fun i : Fin n => D.weight i.val)
          (realValuationOrder (coefficientFractionValuation O D.valuation) (f.coeff β)) β k) :
    ∃ x : D.sourceRing O, x ∈ D.sourceIdeal O ∧ (x : K) = D.evaluation O n f := by
  classical
  have hcoeff' : ∀ β, ∃ c : O, algebraMap O (FractionRing O) c = f.coeff β := by
    intro β
    by_cases hβ : f.coeff β = 0
    · exact ⟨0, by simp [hβ]⟩
    · exact hcoeff β hβ
  choose c hc using hcoeff'
  let x := ∑ β ∈ f.coeff.support,
    D.sourcePolynomialTerm O (c β) (fun i => (β i).toNat)
  refine ⟨x, ?_, ?_⟩
  · apply (D.sourceIdeal O).sum_mem
    intro β hβ
    have hβ0 : f.coeff β ≠ 0 := Finsupp.mem_support_iff.mp hβ
    have he : (fun i => ((β i).toNat : ℤ)) = β := by
      funext i
      exact Int.toNat_of_nonneg (hnonneg β hβ0 i)
    apply D.sourcePolynomialTerm_mem_sourceIdeal_of_dead O π hπirr hπ hO
    intro _
    have hord : realValuationOrder D.valuation (c β : K) =
        realValuationOrder (coefficientFractionValuation O D.valuation) (f.coeff β) := by
      rw [← hc β]
      simp [realValuationOrder, coefficientFractionValuation]
    simpa only [hord, he] using hdead β hβ0
  · have hf := AddMonoidAlgebra.sum_coeff_single f
    change (∑ β ∈ f.coeff.support, AddMonoidAlgebra.single β (f.coeff β)) = f at hf
    change (D.sourceRing O).subtype (∑ β ∈ f.coeff.support,
      D.sourcePolynomialTerm O (c β) (fun i => (β i).toNat)) = _
    rw [map_sum]
    calc
      _ = ∑ β ∈ f.coeff.support,
          D.evaluation O n (AddMonoidAlgebra.single β (f.coeff β)) := by
        apply Finset.sum_congr rfl
        intro β hβ
        have hβ0 : f.coeff β ≠ 0 := Finsupp.mem_support_iff.mp hβ
        simp only [Subring.subtype_apply, sourcePolynomialTerm_coe,
          evaluation, laurentEvaluation_single]
        rw [← hc β, coefficientFractionEmbedding_algebraMap]
        congr 1
        apply Finset.prod_congr rfl
        intro i _
        calc
          (D.ratio i.val : K) ^ (β i).toNat =
              (D.ratio i.val : K) ^ ((β i).toNat : ℤ) := (zpow_natCast _ _).symm
          _ = (D.ratio i.val : K) ^ β i := by rw [Int.toNat_of_nonneg (hnonneg β hβ0 i)]
      _ = D.evaluation O n f := by rw [← map_sum, hf]

/-- Evaluation takes polynomial members of the model ideal with coefficients in the
original DVR into the source endpoint ideal. -/
theorem exists_sourceIdeal_evaluation_of_mem_modelJunk
    (O : Subring K) [IsDiscreteValuationRing O] (π : O) (hπirr : Irreducible π)
    (hπ : (π : K) = (D.uniformizer : K))
    (hO : ∀ c : O, D.valuation (c : K) ≤ 1)
    {n : ℕ} (f : Laurent (FractionRing O) n)
    (hcoeff : ∀ β, f.coeff β ≠ 0 → ∃ c : O, algebraMap O (FractionRing O) c = f.coeff β)
    (hnonneg : ∀ β, f.coeff β ≠ 0 → ∀ i, 0 ≤ β i)
    (hf : f ∈ modelJunk (coefficientFractionValuation O D.valuation)
      (algebraMap O (FractionRing O) π) (D.modelParameters n)) :
    ∃ x : D.sourceRing O, x ∈ D.sourceIdeal O ∧ (x : K) = D.evaluation O n f := by
  apply D.exists_sourceIdeal_evaluation_of_dead_terms O π hπirr hπ hO f hcoeff hnonneg
  intro β hβ
  have hm := modelJunk_term_meetsLevel (coefficientFractionValuation O D.valuation)
    (algebraMap O (FractionRing O) π) (D.coefficientUniformizer_ne_zero O π hπ)
    (D.coefficientUniformizer_order O π hπ) (D.modelParameters n) hf β hβ
  exact (meetsLevel_endpoint_quotient_iff (D.modelParameters n).weights
    (D.modelParameters n).kappa
    (realValuationOrder (coefficientFractionValuation O D.valuation) (f.coeff β))
    (D.modelParameters n).thresholds β (hnonneg β hβ)).mp hm

/-- The domination conclusion for a specified actual source element whose
field value is the polynomial evaluation. -/
theorem mem_sourceIdeal_of_evaluation_mem_modelJunk
    (O : Subring K) [IsDiscreteValuationRing O] (π : O) (hπirr : Irreducible π)
    (hπ : (π : K) = (D.uniformizer : K))
    (hO : ∀ c : O, D.valuation (c : K) ≤ 1)
    {n : ℕ} (f : Laurent (FractionRing O) n)
    (hcoeff : ∀ β, f.coeff β ≠ 0 → ∃ c : O, algebraMap O (FractionRing O) c = f.coeff β)
    (hnonneg : ∀ β, f.coeff β ≠ 0 → ∀ i, 0 ≤ β i)
    (hf : f ∈ modelJunk (coefficientFractionValuation O D.valuation)
      (algebraMap O (FractionRing O) π) (D.modelParameters n))
    (x : D.sourceRing O) (hx : (x : K) = D.evaluation O n f) : x ∈ D.sourceIdeal O := by
  obtain ⟨y, hy, hye⟩ :=
    D.exists_sourceIdeal_evaluation_of_mem_modelJunk O π hπirr hπ hO f hcoeff hnonneg hf
  have hxy : x = y := Subtype.ext (hx.trans hye.symm)
  simpa only [hxy] using hy

end SourceBlockData
end HereditaryAtomicity.DVRBase
