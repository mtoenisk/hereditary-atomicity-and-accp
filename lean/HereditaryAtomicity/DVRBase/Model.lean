import HereditaryAtomicity.DVRBase.Laurent
import HereditaryAtomicity.DVRBase.ModelOrders

/-!
# The actual generator-defined finite Laurent model

The subring R₀ is generated inside the finite Laurent polynomial ring. Its numerical
support condition follows from those generators.
-/

noncomputable section
namespace HereditaryAtomicity.DVRBase

open scoped BigOperators NNReal

/-- Numerical parameters for the finite model. Cut k includes the first k
variables, in the zero-based Lean indexing. -/
structure ModelParameters (n : ℕ) where
  kappa : ℕ
  kappa_pos : 0 < kappa
  weights : Fin n → ℝ
  weights_pos : ∀ i, 0 < weights i
  thresholds : ℕ → ℝ
  threshold_zero : thresholds 0 = 0
  threshold_large : ∀ k, 0 < k → k ≤ n → 2 * (kappa : ℝ) ≤ thresholds k
  remaining_pos : ∀ k ≤ n, 0 < remainingValue weights kappa k

namespace ModelParameters

variable {n : ℕ} (P : ModelParameters n)

theorem threshold_nonneg (k : ℕ) (hk : k ≤ n) : 0 ≤ P.thresholds k := by
  by_cases h : k = 0
  · simp [h, P.threshold_zero]
  · exact (mul_nonneg (by norm_num) (Nat.cast_nonneg _)).trans
      (P.threshold_large k (Nat.pos_of_ne_zero h) hk)

/-- The numerical condition for membership of a monomial in R₀. -/
def ringClass : MonomialClass n where
  contains β e := MeetsLevel P.weights P.kappa P.thresholds β e
  upward := by
    intro β e f h hf
    exact hf.upward h

theorem ringClass_multiplicative : P.ringClass.IsMultiplicative where
  one_mem := by
    refine ⟨0, Nat.zero_le _, ?_⟩
    simp [P.threshold_zero, levelValue_zero_exponent]
  add_mem := MeetsLevel.add (fun i => (P.weights_pos i).le)
    (fun k hk => (P.remaining_pos k hk).le) (P.threshold_nonneg)

end ModelParameters

variable {K : Type*} [Field K] {n : ℕ}

/-- The literal inverse-variable chain monomial Zₙ. -/
def terminalMonomial (π : K) (κ : ℕ) : Laurent K n :=
  AddMonoidAlgebra.single (fun _ => -1) (π ^ κ)

/-- Exponents involving only the first k variables. -/
def SupportedBefore (β : Fin n → ℤ) (k : ℕ) : Prop :=
  ∀ i, k ≤ i.val → β i = 0

/-- The prescribed generators of the finite ring, including all integral
constants and all high monomials at each nonzero level. -/
inductive ModelGenerator (v : Valuation K ℝ≥0) (π : K) (P : ModelParameters n) :
    Laurent K n → Prop
  | constant (c : K) (hc : v c ≤ 1) : ModelGenerator v π P (AddMonoidAlgebra.single 0 c)
  | coordinate (i : Fin n) : ModelGenerator v π P (variableMonomial i)
  | terminal : ModelGenerator v π P (terminalMonomial π P.kappa)
  | high (k : ℕ) (hk0 : 0 < k) (hkn : k ≤ n) (β : Fin n → ℤ) (c : K)
      (hc : c ≠ 0) (hs : SupportedBefore β k)
      (hv : P.thresholds k ≤ termOrder v P.weights β c) :
      ModelGenerator v π P (AddMonoidAlgebra.single β c)

/-- R₀, defined by its generators as in the manuscript. -/
def modelRing (v : Valuation K ℝ≥0) (π : K) (P : ModelParameters n) :
    Subring (Laurent K n) := Subring.closure {f | ModelGenerator v π P f}

theorem modelRing_constant (v : Valuation K ℝ≥0) (π : K) (P : ModelParameters n)
    (c : K) (hc : v c ≤ 1) : AddMonoidAlgebra.single 0 c ∈ modelRing v π P :=
  Subring.subset_closure (ModelGenerator.constant c hc)

theorem modelRing_variable (v : Valuation K ℝ≥0) (π : K) (P : ModelParameters n)
    (i : Fin n) : variableMonomial i ∈ modelRing v π P :=
  Subring.subset_closure (ModelGenerator.coordinate i)

theorem modelRing_terminal (v : Valuation K ℝ≥0) (π : K) (P : ModelParameters n) :
    terminalMonomial π P.kappa ∈ modelRing v π P :=
  Subring.subset_closure ModelGenerator.terminal

theorem modelRing_high (v : Valuation K ℝ≥0) (π : K) (P : ModelParameters n)
    (k : ℕ) (hk0 : 0 < k) (hkn : k ≤ n) (β : Fin n → ℤ) (c : K)
    (hc : c ≠ 0) (hs : SupportedBefore β k)
    (hv : P.thresholds k ≤ termOrder v P.weights β c) :
    AddMonoidAlgebra.single β c ∈ modelRing v π P :=
  Subring.subset_closure (ModelGenerator.high k hk0 hkn β c hc hs hv)

theorem modelRing_nonneg_monomial (v : Valuation K ℝ≥0) (π : K) (P : ModelParameters n)
    (β : Fin n → ℤ) (hβ : ∀ i, 0 ≤ β i) (c : K) (hc : v c ≤ 1) :
    AddMonoidAlgebra.single β c ∈ modelRing v π P :=
  single_nonneg_mem_subring _ (modelRing_variable v π P) β hβ c (modelRing_constant v π P c hc)

/-- Every generator, hence every term of every element of R₀, satisfies the
numerical level criterion. -/
theorem modelRing_le_supported (v : Valuation K ℝ≥0) (π : K)
    (hπ : realValuationOrder v π = 1) (P : ModelParameters n) :
    modelRing v π P ≤ P.ringClass.supportedSubring v P.ringClass_multiplicative := by
  apply Subring.closure_le.mpr
  intro f hf
  change f ∈ P.ringClass.supported v
  cases hf with
  | constant c hc =>
      apply (MonomialClass.single_mem_supported v P.ringClass 0 c).mpr
      by_cases hc0 : c = 0
      · exact Or.inl hc0
      · exact Or.inr (MeetsLevel.of_nonneg P.threshold_zero.le
          ((realValuationOrder_nonneg_iff v hc0).mpr hc) (by simp))
  | coordinate i =>
      change AddMonoidAlgebra.single (Pi.single i 1) 1 ∈ P.ringClass.supported v
      apply (MonomialClass.single_mem_supported v P.ringClass _ _).mpr
      right
      apply MeetsLevel.of_nonneg P.threshold_zero.le (by simp)
      intro j
      simp only [Pi.single_apply]
      split_ifs <;> norm_num
  | terminal =>
      apply (MonomialClass.single_mem_supported v P.ringClass _ _).mpr
      right
      refine ⟨0, Nat.zero_le _, ?_⟩
      have hd : (poleTail (fun _ : Fin n => (-1 : ℤ)) 0 : ℝ) ≤ 1 := by
        exact_mod_cast (poleTail_le_iff (fun _ : Fin n => (-1 : ℤ)) 0 1).mpr
          ⟨by norm_num, by intros; norm_num⟩
      have hm := mul_le_mul_of_nonneg_right hd (Nat.cast_nonneg P.kappa : (0 : ℝ) ≤ _)
      simp only [P.threshold_zero, levelValue, partialValue_zero, remainingValue_zero,
        realValuationOrder_pow, hπ, mul_one]
      linarith
  | high k hk0 hkn β c hc hs hv =>
      exact (MonomialClass.single_mem_supported v P.ringClass β c).mpr
        (Or.inr (MeetsLevel.of_tail_zero hkn hs hv))

/-- Nonzero coefficients of an element of the generated ring satisfy an
actual level inequality, even after cancellation has collected coefficients. -/
theorem modelRing_term_meetsLevel (v : Valuation K ℝ≥0) (π : K)
    (hπ : realValuationOrder v π = 1) (P : ModelParameters n)
    {f : Laurent K n} (hf : f ∈ modelRing v π P)
    (β : Fin n → ℤ) (hβ : f.coeff β ≠ 0) :
    MeetsLevel P.weights P.kappa P.thresholds β (realValuationOrder v (f.coeff β)) :=
  (MonomialClass.mem_supported v P.ringClass).mp (modelRing_le_supported v π hπ P hf) β hβ

theorem modelRing_termOrder_nonneg (v : Valuation K ℝ≥0) (π : K)
    (hπ : realValuationOrder v π = 1) (P : ModelParameters n)
    {f : Laurent K n} (hf : f ∈ modelRing v π P)
    (β : Fin n → ℤ) (hβ : f.coeff β ≠ 0) :
    0 ≤ termOrder v P.weights β (f.coeff β) :=
  (modelRing_term_meetsLevel v π hπ P hf β hβ).nonneg_total
    (fun i => (P.weights_pos i).le) (fun k hk => (P.remaining_pos k hk).le) P.threshold_nonneg

/-- The explicit monomial normal form proves the converse to the numerical
criterion. All factors belong to the generator-defined ring. -/
theorem modelRing_single_of_meetsLevel (v : Valuation K ℝ≥0) (π : K)
    (hπ0 : π ≠ 0) (hπ : realValuationOrder v π = 1) (P : ModelParameters n)
    (β : Fin n → ℤ) (c : K) (hc : c ≠ 0)
    (h : MeetsLevel P.weights P.kappa P.thresholds β (realValuationOrder v c)) :
    AddMonoidAlgebra.single β c ∈ modelRing v π P := by
  classical
  obtain ⟨k, hkn, hk⟩ := h
  let d : ℕ := (poleTail β k).toNat
  let b : K := (π ^ P.kappa) ^ d
  have hd : (d : ℤ) = poleTail β k := Int.toNat_of_nonneg (poleTail_nonneg β k)
  have hdr : (d : ℝ) = (poleTail β k : ℝ) := by exact_mod_cast hd
  have hb : b ≠ 0 := pow_ne_zero _ (pow_ne_zero _ hπ0)
  have hcb : c / b ≠ 0 := div_ne_zero hc hb
  have hhead : termOrder v P.weights (modelHeadExponent β k) (c / b) =
      levelValue P.weights P.kappa (realValuationOrder v c) β k := by
    rw [termOrder, realValuationOrder_div v hc hb]
    simp only [b, realValuationOrder_pow, hπ, mul_one, hdr]
    convert modelHeadExponent_order P.weights P.kappa (realValuationOrder v c) β k using 1
    ring
  have hheadmem : AddMonoidAlgebra.single (modelHeadExponent β k) (c / b) ∈ modelRing v π P := by
    by_cases hk0 : k = 0
    · subst k
      rw [modelHeadExponent_zero]
      apply modelRing_constant
      apply (realValuationOrder_nonneg_iff v hcb).mp
      have hh := hk.trans_eq hhead.symm
      simpa [termOrder, P.threshold_zero] using hh
    · exact modelRing_high v π P k (Nat.pos_of_ne_zero hk0) hkn _ _ hcb
        (modelHeadExponent_tail β k) (hk.trans_eq hhead.symm)
  have htailmem : AddMonoidAlgebra.single (modelTailExponent β k) (1 : K) ∈ modelRing v π P :=
    modelRing_nonneg_monomial v π P _ (modelTailExponent_nonneg β k) 1 (by simp)
  have hpow : (terminalMonomial π P.kappa : Laurent K n) ^ d =
      AddMonoidAlgebra.single (fun _ => -poleTail β k) b := by
    simp only [terminalMonomial, AddMonoidAlgebra.single_pow]
    congr 1
    funext i
    simp [Pi.smul_apply, hd]
  have heq : (AddMonoidAlgebra.single (modelHeadExponent β k) (c / b) *
        (terminalMonomial π P.kappa : Laurent K n) ^ d) *
        AddMonoidAlgebra.single (modelTailExponent β k) 1 = AddMonoidAlgebra.single β c := by
    rw [hpow, AddMonoidAlgebra.single_mul_single, AddMonoidAlgebra.single_mul_single,
      modelExponent_decomposition, div_mul_cancel₀ _ hb, mul_one]
  rw [← heq]
  exact (modelRing v π P).mul_mem
    ((modelRing v π P).mul_mem hheadmem ((modelRing v π P).pow_mem (modelRing_terminal v π P) d))
    htailmem

/-- Lemma 6.5(b): the generator-defined ring is exactly the termwise level support ring. -/
theorem modelRing_eq_supported (v : Valuation K ℝ≥0) (π : K)
    (hπ0 : π ≠ 0) (hπ : realValuationOrder v π = 1) (P : ModelParameters n) :
    modelRing v π P = P.ringClass.supportedSubring v P.ringClass_multiplicative := by
  classical
  apply le_antisymm (modelRing_le_supported v π hπ P)
  intro f hf
  rw [← AddMonoidAlgebra.sum_coeff_single f, Finsupp.sum]
  apply Subring.sum_mem
  intro β hβ
  have hn := Finsupp.mem_support_iff.mp hβ
  apply modelRing_single_of_meetsLevel v π hπ0 hπ P β _ hn
  exact (MonomialClass.mem_supported v P.ringClass).mp hf β hn

theorem modelRing_single_iff (v : Valuation K ℝ≥0) (π : K)
    (hπ0 : π ≠ 0) (hπ : realValuationOrder v π = 1) (P : ModelParameters n)
    (β : Fin n → ℤ) (c : K) (hc : c ≠ 0) :
    AddMonoidAlgebra.single β c ∈ modelRing v π P ↔
      MeetsLevel P.weights P.kappa P.thresholds β (realValuationOrder v c) := by
  rw [modelRing_eq_supported v π hπ0 hπ P, MonomialClass.mem_supportedSubring,
    MonomialClass.single_mem_supported, or_iff_right hc]
  rfl

end HereditaryAtomicity.DVRBase
