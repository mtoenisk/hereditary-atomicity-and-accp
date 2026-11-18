import HereditaryAtomicity.DVRBase.ModelSource
import HereditaryAtomicity.DVRBase.Gauss
import HereditaryAtomicity.DVRBase.ModelG3Numerics

/-! Initial terms and the shape of factors in the finite model obstruction. -/

noncomputable section
namespace HereditaryAtomicity.DVRBase
open scoped BigOperators NNReal
variable {K : Type*} [Field K] {n : ℕ}

theorem IsInitialTerm.eq {v : Valuation K ℝ≥0} {u : Fin n → ℝ}
    {f : Laurent K n} {β γ : Fin n → ℤ}
    (hβ : IsInitialTerm v u f β) (hγ : IsInitialTerm v u f γ) : β = γ := by
  by_contra hne
  have h1 := hβ.2 γ (Ne.symm hne) hγ.1
  have h2 := hγ.2 β hne hβ.1
  exact (lt_asymm h1 h2)

theorem isInitialTerm_one_add_of_positive (v : Valuation K ℝ≥0) (u : Fin n → ℝ)
    (j : Laurent K n)
    (hj : ∀ β, j.coeff β ≠ 0 → 0 < termOrder v u β (j.coeff β)) :
    IsInitialTerm v u (1 + j) 0 ∧ realValuationOrder v ((1 + j).coeff 0) = 0 := by
  classical
  have hzero : (1 + j).coeff 0 = 1 + j.coeff 0 := by
    change (AddMonoidAlgebra.single 0 (1 : K) + j).coeff 0 = _
    simp
  have hval : v (1 + j.coeff 0) = 1 := by
    by_cases hj0 : j.coeff 0 = 0
    · simp [hj0]
    · have hpos : 0 < realValuationOrder v (j.coeff 0) := by
        simpa [termOrder] using hj 0 hj0
      have hv := (realValuationOrder_pos_iff v hj0).mp hpos
      simpa using v.map_add_eq_of_lt_left (show v (j.coeff 0) < v 1 by simpa)
  have hnonzero : (1 + j).coeff 0 ≠ 0 := by
    intro h
    rw [hzero] at h
    have := hval
    rw [h, map_zero] at this
    exact zero_ne_one this
  have horder : realValuationOrder v ((1 + j).coeff 0) = 0 := by
    simp [realValuationOrder, hval]
  refine ⟨⟨hnonzero, fun β hβ hc => ?_⟩, horder⟩
  have hcoeff : (1 + j).coeff β = j.coeff β := by
    change (AddMonoidAlgebra.single 0 (1 : K) + j).coeff β = _
    simp [hβ]
  have hp := hj β (hcoeff ▸ hc)
  rw [termOrder, termOrder, horder, hcoeff]
  simpa only [termOrder, Pi.zero_apply, Int.cast_zero, zero_mul, Finset.sum_const_zero, zero_add] using hp

theorem modelJunk_one_add_initial (v : Valuation K ℝ≥0) (π : K)
    (hπ0 : π ≠ 0) (hπ : realValuationOrder v π = 1) (P : ModelParameters n)
    {j : Laurent K n} (hj : j ∈ modelJunk v π P) :
    IsInitialTerm v P.weights (1 + j) 0 ∧
      realValuationOrder v ((1 + j).coeff 0) = 0 :=
  isInitialTerm_one_add_of_positive v P.weights j
    (modelJunk_termOrder_pos v π hπ0 hπ P hj)

theorem endpointMonomial_initial (v : Valuation K ℝ≥0) (π : K) (hπ0 : π ≠ 0)
    (P : ModelParameters n) (k : ℕ) :
    IsInitialTerm v P.weights (endpointMonomial π P.kappa k)
      (fun i => if i.val < k then -1 else 0) :=
  isInitialTerm_single v P.weights _ (pow_ne_zero _ hπ0)

theorem endpointMonomial_one_add_initial (v : Valuation K ℝ≥0) (π : K)
    (hπ0 : π ≠ 0) (hπ : realValuationOrder v π = 1) (P : ModelParameters n)
    (k : ℕ) {j : Laurent K n} (hj : j ∈ modelJunk v π P) :
    IsInitialTerm v P.weights (endpointMonomial π P.kappa k * (1 + j))
      (fun i => if i.val < k then -1 else 0) ∧
      realValuationOrder v ((endpointMonomial π P.kappa k * (1 + j)).coeff
        (fun i => if i.val < k then -1 else 0)) = P.kappa := by
  have hZ := endpointMonomial_initial v π hπ0 P k
  obtain ⟨hplus, hcoeff⟩ := modelJunk_one_add_initial v π hπ0 hπ P hj
  refine ⟨by simpa only [add_zero] using hZ.mul hplus, ?_⟩
  have h := hZ.coefficientOrder_mul hplus
  rw [hcoeff, add_zero] at h
  simpa [endpointMonomial, realValuationOrder_pow, hπ] using h

theorem endpoint_termOrder (v : Valuation K ℝ≥0) (π : K)
    (hπ : realValuationOrder v π = 1) (P : ModelParameters n) (k : ℕ) :
    termOrder v P.weights (fun i => if i.val < k then -1 else 0) (π ^ P.kappa) =
      remainingValue P.weights P.kappa k := by
  simp only [termOrder, realValuationOrder_pow, hπ, mul_one, remainingValue,
    prefixSum, Finset.sum_filter]
  rw [sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> simp

theorem IsInitialTerm.finset_coefficientOrder {v : Valuation K ℝ≥0}
    {u : Fin n → ℝ} {ι : Type*} (s : Finset ι) (f : ι → Laurent K n)
    (β : ι → Fin n → ℤ) (h : ∀ i ∈ s, IsInitialTerm v u (f i) (β i)) :
    realValuationOrder v ((∏ i ∈ s, f i).coeff (∑ i ∈ s, β i)) =
      ∑ i ∈ s, realValuationOrder v ((f i).coeff (β i)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    have hs := fun i hi => h i (Finset.mem_insert_of_mem hi)
    rw [Finset.prod_insert ha, Finset.sum_insert ha, Finset.sum_insert ha]
    rw [(h a (Finset.mem_insert_self _ _)).coefficientOrder_mul
      (IsInitialTerm.finset_prod s f β hs), ih hs]

/-- Every factor in a finite product with one initial term has an initial
term, and their exponents and coefficient orders add to those of the product. -/
theorem IsInitialTerm.finset_factor_data {v : Valuation K ℝ≥0} {u : Fin n → ℝ}
    {ι : Type*} (s : Finset ι) (f : ι → Laurent K n)
    {δ : Fin n → ℤ} (h : IsInitialTerm v u (∏ i ∈ s, f i) δ) :
    ∃ β : ι → Fin n → ℤ, (∀ i ∈ s, IsInitialTerm v u (f i) (β i)) ∧
      (∑ i ∈ s, β i) = δ ∧
      (∑ i ∈ s, realValuationOrder v ((f i).coeff (β i))) =
        realValuationOrder v ((∏ i ∈ s, f i).coeff δ) := by
  classical
  have hex : ∀ i, i ∈ s → ∃ β, IsInitialTerm v u (f i) β := by
    intro i hi
    obtain ⟨β, hβ⟩ := h.subproduct f (Finset.singleton_subset_iff.mpr hi)
    exact ⟨β, by simpa using hβ⟩
  let β : ι → Fin n → ℤ := fun i => if hi : i ∈ s then (hex i hi).choose else 0
  have hβ : ∀ i ∈ s, IsInitialTerm v u (f i) (β i) := by
    intro i hi
    simpa only [β, dite_eq_left hi] using (hex i hi).choose_spec
  have hsum := (IsInitialTerm.finset_prod s f β hβ).eq h
  refine ⟨β, hβ, hsum, ?_⟩
  rw [← hsum]
  exact (IsInitialTerm.finset_coefficientOrder s f β hβ).symm

theorem IsInitialTerm.finset_order {v : Valuation K ℝ≥0}
    {u : Fin n → ℝ} {ι : Type*} (s : Finset ι) (f : ι → Laurent K n)
    (β : ι → Fin n → ℤ) (h : ∀ i ∈ s, IsInitialTerm v u (f i) (β i)) :
    termOrder v u (∑ i ∈ s, β i) ((∏ i ∈ s, f i).coeff (∑ i ∈ s, β i)) =
      ∑ i ∈ s, termOrder v u (β i) ((f i).coeff (β i)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [termOrder]
  | @insert a s ha ih =>
    have hs := fun i hi => h i (Finset.mem_insert_of_mem hi)
    rw [Finset.prod_insert ha, Finset.sum_insert ha, Finset.sum_insert ha]
    rw [(h a (Finset.mem_insert_self _ _)).order_mul
      (IsInitialTerm.finset_prod s f β hs), ih hs]

theorem endpoint_factor_initial_data (v : Valuation K ℝ≥0) (π : K)
    (hπ0 : π ≠ 0) (hπ : realValuationOrder v π = 1) (P : ModelParameters n)
    {ι : Type*} (s : Finset ι) (f : ι → Laurent K n) (k : ℕ)
    {j : Laurent K n} (hj : j ∈ modelJunk v π P)
    (hprod : (∏ i ∈ s, f i) = endpointMonomial π P.kappa k * (1 + j)) :
    ∃ β : ι → Fin n → ℤ, (∀ i ∈ s, IsInitialTerm v P.weights (f i) (β i)) ∧
      (∑ i ∈ s, β i) = (fun l => if l.val < k then -1 else 0) ∧
      (∑ i ∈ s, realValuationOrder v ((f i).coeff (β i))) = P.kappa ∧
      (∑ i ∈ s, termOrder v P.weights (β i) ((f i).coeff (β i))) =
        remainingValue P.weights P.kappa k := by
  obtain ⟨hinit, hcoeff⟩ := endpointMonomial_one_add_initial v π hπ0 hπ P k hj
  rw [← hprod] at hinit hcoeff
  obtain ⟨β, hβ, hexp, he⟩ := hinit.finset_factor_data s f
  refine ⟨β, hβ, hexp, he.trans hcoeff, ?_⟩
  rw [← IsInitialTerm.finset_order s f β hβ, hexp, termOrder, hcoeff]
  have h := endpoint_termOrder v π hπ P k
  simpa only [termOrder, realValuationOrder_pow, hπ, mul_one] using h

theorem modelSourceRing_low_initial_coefficient (v : Valuation K ℝ≥0) (π : K)
    (hπ0 : π ≠ 0) (hπ : realValuationOrder v π = 1) (P : ModelParameters n)
    (Λ : Finset (Fin n)) {f : Laurent K n} (hf : f ∈ modelSourceRing v π P Λ)
    {β : Fin n → ℤ} (hβ : IsInitialTerm v P.weights f β)
    (hsmall : termOrder v P.weights β (f.coeff β) < 2 * (P.kappa : ℝ)) :
    0 ≤ realValuationOrder v (f.coeff β) := by
  by_cases hj : AddMonoidAlgebra.single β (f.coeff β) ∈ modelJunk v π P
  · exact (Nat.cast_nonneg P.kappa).trans
      (modelJunk_low_coefficient v π hπ0 hπ P β _ hβ.1 hj hsmall)
  · exact (modelSourceRing_nonjunk_term v π hπ0 hπ P Λ hf β hβ.1 hj).1

/-- A finite nonnegative coefficient-order budget has only one term at least
the whole positive budget; all other orders vanish. -/
theorem unique_large_in_sum {ι : Type*} (s : Finset ι) (e : ι → ℝ)
    {κ : ℝ} (hne : ∀ i ∈ s, 0 ≤ e i)
    (hsum : ∑ i ∈ s, e i = κ) {i₀ : ι} (hi₀ : i₀ ∈ s) (hlarge : κ ≤ e i₀) :
    e i₀ = κ ∧ ∀ i ∈ s, i ≠ i₀ → e i = 0 := by
  classical
  have heq : e i₀ = κ := le_antisymm
    (hsum ▸ Finset.single_le_sum hne hi₀) hlarge
  refine ⟨heq, fun i hi hni => ?_⟩
  have hrest : ∑ k ∈ s.erase i₀, e k = 0 := by
    have h := Finset.sum_erase_add s e hi₀
    rw [hsum, heq] at h
    linarith
  have hle : e i ≤ 0 := by
    rw [← hrest]
    exact Finset.single_le_sum (fun k hk => hne k (Finset.mem_of_mem_erase hk))
      (Finset.mem_erase.mpr ⟨hni, hi⟩)
  exact le_antisymm hle (hne i hi)

/-- The product equation of Theorem F forces exactly one initial monomial
into J₀. Its coefficient order is κ; every other initial coefficient has
order zero and its exponent is a nonnegative selected-variable exponent. -/
theorem modelProduct_unique_exceptional (v : Valuation K ℝ≥0) (π : K)
    (hπ0 : π ≠ 0) (hπ : realValuationOrder v π = 1) (P : ModelParameters n)
    (hn : 0 < n) (Λ : Finset (Fin n)) {ι : Type*} (s : Finset ι)
    (f : ι → Laurent K n) (hf : ∀ i ∈ s, f i ∈ modelSourceRing v π P Λ)
    {j : Laurent K n} (hj : j ∈ modelJunk v π P)
    (hprod : (∏ i ∈ s, f i) = endpointMonomial π P.kappa 1 * (1 + j)) :
    ∃ (β : ι → Fin n → ℤ) (i₀ : ι),
      (∀ i ∈ s, IsInitialTerm v P.weights (f i) (β i)) ∧
      (∑ i ∈ s, β i) = (fun l => if l.val < 1 then -1 else 0) ∧
      i₀ ∈ s ∧ AddMonoidAlgebra.single (β i₀) ((f i₀).coeff (β i₀)) ∈ modelJunk v π P ∧
      realValuationOrder v ((f i₀).coeff (β i₀)) = P.kappa ∧
      (∀ l, 0 ≤ β i₀ l + 1) ∧
      ∀ i ∈ s, i ≠ i₀ →
        realValuationOrder v ((f i).coeff (β i)) = 0 ∧
        AddMonoidAlgebra.single (β i) ((f i).coeff (β i)) ∉ modelJunk v π P ∧
        (∀ l, 0 ≤ β i l) ∧ (∀ l, l ∉ Λ → β i l = 0) := by
  classical
  obtain ⟨β, hβ, hexp, he, horder⟩ := endpoint_factor_initial_data v π hπ0 hπ P s f 1 hj hprod
  have hvnonneg : ∀ i ∈ s, 0 ≤ termOrder v P.weights (β i) ((f i).coeff (β i)) := by
    intro i hi
    exact modelRing_termOrder_nonneg v π hπ P
      (modelSourceRing_le_modelRing v π P Λ (hf i hi)) (β i) (hβ i hi).1
  have hκ : (0 : ℝ) < P.kappa := by exact_mod_cast P.kappa_pos
  have hprefix : 0 ≤ prefixSum P.weights 1 := by
    exact Finset.sum_nonneg (fun i _ => (P.weights_pos i).le)
  have htotal : remainingValue P.weights P.kappa 1 < 2 * (P.kappa : ℝ) := by
    unfold remainingValue
    linarith
  have hsmall : ∀ i ∈ s, termOrder v P.weights (β i) ((f i).coeff (β i)) <
      2 * (P.kappa : ℝ) := by
    intro i hi
    have hle := Finset.single_le_sum hvnonneg hi
    rw [horder] at hle
    exact hle.trans_lt htotal
  have henonneg : ∀ i ∈ s, 0 ≤ realValuationOrder v ((f i).coeff (β i)) := by
    intro i hi
    exact modelSourceRing_low_initial_coefficient v π hπ0 hπ P Λ
      (hf i hi) (hβ i hi) (hsmall i hi)
  have hfirst : (∑ i ∈ s, β i ⟨0, hn⟩) = -1 := by
    have h := congrFun hexp ⟨0, hn⟩
    simpa using h
  have hexists : ∃ i ∈ s,
      AddMonoidAlgebra.single (β i) ((f i).coeff (β i)) ∈ modelJunk v π P := by
    by_contra! hnone
    have hnonneg : (0 : ℤ) ≤ ∑ i ∈ s, β i ⟨0, hn⟩ := by
      apply Finset.sum_nonneg
      intro i hi
      exact (modelSourceRing_nonjunk_term v π hπ0 hπ P Λ (hf i hi) (β i)
        (hβ i hi).1 (hnone i hi)).2.1 ⟨0, hn⟩
    rw [hfirst] at hnonneg
    omega
  obtain ⟨i₀, hi₀, hji₀⟩ := hexists
  have hlarge := modelJunk_low_coefficient v π hπ0 hπ P (β i₀) _ (hβ i₀ hi₀).1
    hji₀ (hsmall i₀ hi₀)
  obtain ⟨hei₀, hothers⟩ := unique_large_in_sum s
    (fun i => realValuationOrder v ((f i).coeff (β i))) henonneg he hi₀ hlarge
  refine ⟨β, i₀, hβ, hexp, hi₀, hji₀, hei₀,
    modelJunk_low_exponent v π hπ0 hπ P (β i₀) _ (hβ i₀ hi₀).1 hji₀ hei₀
      (hsmall i₀ hi₀), fun i hi hni => ?_⟩
  have hei := hothers i hi hni
  have hnot : AddMonoidAlgebra.single (β i) ((f i).coeff (β i)) ∉ modelJunk v π P := by
    intro hmem
    have hge := modelJunk_low_coefficient v π hπ0 hπ P (β i) _ (hβ i hi).1
      hmem (hsmall i hi)
    rw [hei] at hge
    exact (not_le_of_gt hκ) hge
  exact ⟨hei, hnot, (modelSourceRing_nonjunk_term v π hπ0 hπ P Λ (hf i hi) (β i)
    (hβ i hi).1 hnot).2⟩

/-- Coordinate comparison in Step 1 gives a partition of all coordinates
after the first. This includes an empty complementary product. -/
theorem squarefree_partition_of_exponent_sum {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (β : ι → Fin n → ℤ) {i₀ : ι} (hi₀ : i₀ ∈ s) (Λ : Finset (Fin n))
    (hsum : (∑ i ∈ s, β i) = (fun l => if l.val < 1 then -1 else 0))
    (hex : ∀ l, 0 ≤ β i₀ l + 1)
    (hpos : ∀ i ∈ s, i ≠ i₀ → ∀ l, 0 ≤ β i l)
    (hsupp : ∀ i ∈ s, i ≠ i₀ → ∀ l, l ∉ Λ → β i l = 0) :
    ∃ L D : Finset (Fin n), Disjoint L D ∧
      L ∪ D = Finset.univ.filter (fun l => 0 < l.val) ∧ L ⊆ Λ ∧
      (∑ i ∈ s.erase i₀, β i) = maskExponent L ∧
      β i₀ = (fun l => -1 + maskExponent D l) := by
  classical
  let δ : Fin n → ℤ := ∑ i ∈ s.erase i₀, β i
  let γ : Fin n → ℤ := fun l => β i₀ l + 1
  have hδ : ∀ l, 0 ≤ δ l := by
    intro l
    change 0 ≤ (∑ i ∈ s.erase i₀, β i) l
    simp only [Finset.sum_apply]
    exact Finset.sum_nonneg (fun i hi => hpos i (Finset.mem_of_mem_erase hi)
      (Finset.ne_of_mem_erase hi) l)
  have heq : ∀ l, δ l + γ l = if l.val < 1 then 0 else 1 := by
    intro l
    have h := congrFun (Finset.sum_erase_add s β hi₀) l
    rw [hsum] at h
    simp only [Pi.add_apply] at h
    dsimp [δ, γ]
    split_ifs at * <;> omega
  let L := Finset.univ.filter (fun l => δ l = 1)
  let D := Finset.univ.filter (fun l => γ l = 1)
  have hδ01 : ∀ l, δ l = 0 ∨ δ l = 1 := by
    intro l
    have h1 := hδ l
    have h2 := hex l
    have h3 := heq l
    dsimp [γ] at h3
    split_ifs at h3 <;> omega
  have hγ01 : ∀ l, γ l = 0 ∨ γ l = 1 := by
    intro l
    have h1 := hδ l
    have h2 := hex l
    have h3 := heq l
    change 0 ≤ γ l at h2
    split_ifs at h3 <;> omega
  refine ⟨L, D, ?_, ?_, ?_, ?_, ?_⟩
  · apply Finset.disjoint_left.mpr
    intro l hl hd
    have hL : δ l = 1 := (Finset.mem_filter.mp hl).2
    have hD : γ l = 1 := (Finset.mem_filter.mp hd).2
    have h := heq l
    split_ifs at h <;> omega
  · ext l
    simp only [L, D, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    have h1 := hδ01 l
    have h2 := hγ01 l
    have h3 := heq l
    split_ifs at h3 <;> omega
  · intro l hl
    by_contra hnot
    have hzero : δ l = 0 := by
      simp only [δ, Finset.sum_apply]
      apply Finset.sum_eq_zero
      intro i hi
      exact hsupp i (Finset.mem_of_mem_erase hi) (Finset.ne_of_mem_erase hi) l hnot
    have hone : δ l = 1 := (Finset.mem_filter.mp hl).2
    omega
  · funext l
    change δ l = _
    simp only [maskExponent, L, Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hδ01 l with h | h <;> simp [h]
  · funext l
    have h := hγ01 l
    simp only [maskExponent, D, Finset.mem_filter, Finset.mem_univ, true_and]
    dsimp [γ] at *
    split_ifs <;> omega

/-- Normalizing an initial coefficient of order zero stays in the source
ring and makes the literal initial coefficient equal to one. -/
theorem modelSourceRing_normalize_initial (v : Valuation K ℝ≥0) (π : K)
    (P : ModelParameters n) (Λ : Finset (Fin n)) {q' : Laurent K n}
    (hq' : q' ∈ modelSourceRing v π P Λ) {α : Fin n → ℤ}
    (hinit : IsInitialTerm v P.weights q' α)
    (hc : realValuationOrder v (q'.coeff α) = 0) :
    let q := AddMonoidAlgebra.single 0 (q'.coeff α)⁻¹ * q'
    q ∈ modelSourceRing v π P Λ ∧ IsInitialTerm v P.weights q α ∧ q.coeff α = 1 := by
  dsimp only
  have hinv : (q'.coeff α)⁻¹ ≠ 0 := inv_ne_zero hinit.1
  have hnonneg : 0 ≤ realValuationOrder v (q'.coeff α)⁻¹ := by
    simp [hc]
  have hconst := modelPolynomialRing_constant v Λ _
    ((realValuationOrder_nonneg_iff v hinv).mp hnonneg)
  refine ⟨(modelSourceRing v π P Λ).mul_mem
    (modelPolynomialRing_le_modelSourceRing v π P Λ hconst) hq', ?_, ?_⟩
  · simpa using (isInitialTerm_single v P.weights 0 hinv).mul hinit
  · simp [hinit.1]

/-- Subtracting a Laurent polynomial with initial term exactly one leaves
only strictly positive terms, including the case where the difference is zero. -/
theorem one_sub_positive_of_initial_one (v : Valuation K ℝ≥0) (u : Fin n → ℝ)
    {g : Laurent K n} (hinit : IsInitialTerm v u g 0) (hcoeff : g.coeff 0 = 1) :
    ∀ β, (1 - g).coeff β ≠ 0 → 0 < termOrder v u β ((1 - g).coeff β) := by
  classical
  intro β hβ
  have hne : β ≠ 0 := by
    intro h
    subst β
    apply hβ
    change (AddMonoidAlgebra.single 0 (1 : K) - g).coeff 0 = 0
    simp [hcoeff]
  have heq : (1 - g).coeff β = -g.coeff β := by
    change (AddMonoidAlgebra.single 0 (1 : K) - g).coeff β = _
    simp [hne]
  have hc : g.coeff β ≠ 0 := by simpa only [heq, neg_ne_zero] using hβ
  have h := hinit.2 β hne hc
  rw [heq]
  simpa only [termOrder, hcoeff, realValuationOrder_one, Pi.zero_apply, Int.cast_zero,
    zero_mul, Finset.sum_const_zero, add_zero, realValuationOrder_neg] using h

/-- The normalized complementary product gives the positive error d of
Theorem F, and its translate Y_L d belongs to the source ring. -/
theorem modelSourceRing_initial_error (v : Valuation K ℝ≥0) (π : K)
    (P : ModelParameters n) (Λ L : Finset (Fin n)) (hL : L ⊆ Λ)
    {q : Laurent K n} (hq : q ∈ modelSourceRing v π P Λ)
    (hinit : IsInitialTerm v P.weights q (maskExponent L))
    (hcoeff : q.coeff (maskExponent L) = 1) :
    let YL : Laurent K n := AddMonoidAlgebra.single (maskExponent L) 1
    let d := 1 - AddMonoidAlgebra.single (-maskExponent L) 1 * q
    (∀ β, d.coeff β ≠ 0 → 0 < termOrder v P.weights β (d.coeff β)) ∧
      YL * d = YL - q ∧ YL * d ∈ modelSourceRing v π P Λ := by
  classical
  dsimp only
  have hunit := isInitialTerm_single v P.weights (-maskExponent L)
    (one_ne_zero : (1 : K) ≠ 0)
  have hzero : IsInitialTerm v P.weights
      (AddMonoidAlgebra.single (-maskExponent L) 1 * q) 0 := by
    simpa using hunit.mul hinit
  have hone : (AddMonoidAlgebra.single (-maskExponent L) (1 : K) * q).coeff 0 = 1 := by
    simpa using hcoeff
  have heq : (AddMonoidAlgebra.single (maskExponent L) (1 : K) : Laurent K n) *
      (1 - AddMonoidAlgebra.single (-maskExponent L) 1 * q) =
        AddMonoidAlgebra.single (maskExponent L) 1 - q := by
    rw [mul_sub, mul_one, ← mul_assoc, AddMonoidAlgebra.single_mul_single]
    simp only [add_neg_cancel, mul_one]
    congr 1
    change 1 * q = q
    exact one_mul q
  have hYL : (AddMonoidAlgebra.single (maskExponent L) (1 : K) : Laurent K n) ∈
      modelSourceRing v π P Λ := by
    apply modelPolynomialRing_le_modelSourceRing v π P Λ
    apply modelPolynomialRing_single v Λ _
    · intro l
      simp only [maskExponent]
      split_ifs <;> omega
    · intro l hl
      have hn : l ∉ L := fun h => hl (hL h)
      simp [maskExponent, hn]
    · simp
  exact ⟨one_sub_positive_of_initial_one v P.weights hzero hone, heq,
    heq ▸ (modelSourceRing v π P Λ).sub_mem hYL hq⟩

/-- The concrete output of Step 1 of the finite factorization obstruction.
`coefficient` is the collected initial coefficient of the complementary
product, and both normalization and the error use literal Laurent products. -/
structure ModelProductShape (v : Valuation K ℝ≥0) (π : K) (P : ModelParameters n)
    (Λ : Finset (Fin n)) {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f : ι → Laurent K n) where
  exceptional : ι
  exceptional_mem : exceptional ∈ s
  initialExponent : ι → Fin n → ℤ
  initial : ∀ i ∈ s, IsInitialTerm v P.weights (f i) (initialExponent i)
  exceptional_initial_junk : AddMonoidAlgebra.single (initialExponent exceptional)
    ((f exceptional).coeff (initialExponent exceptional)) ∈ modelJunk v π P
  exceptional_coefficient_order :
    realValuationOrder v ((f exceptional).coeff (initialExponent exceptional)) = P.kappa
  other_coefficient_order : ∀ i ∈ s, i ≠ exceptional →
    realValuationOrder v ((f i).coeff (initialExponent i)) = 0
  left : Finset (Fin n)
  right : Finset (Fin n)
  disjoint : Disjoint left right
  partition : left ∪ right = Finset.univ.filter (fun l => 0 < l.val)
  left_subset : left ⊆ Λ
  other_exponent : (∑ i ∈ s.erase exceptional, initialExponent i) = maskExponent left
  exceptional_exponent : initialExponent exceptional =
    (fun l => -1 + maskExponent right l)
  coefficient : K
  coefficient_eq : coefficient = (∏ i ∈ s.erase exceptional, f i).coeff (maskExponent left)
  coefficient_ne_zero : coefficient ≠ 0
  coefficient_order : realValuationOrder v coefficient = 0
  normalized : Laurent K n
  normalized_eq : normalized = AddMonoidAlgebra.single 0 coefficient⁻¹ *
    (∏ i ∈ s.erase exceptional, f i)
  normalized_mem : normalized ∈ modelSourceRing v π P Λ
  normalized_initial : IsInitialTerm v P.weights normalized (maskExponent left)
  normalized_coefficient : normalized.coeff (maskExponent left) = 1
  scaled_normalized : AddMonoidAlgebra.single 0 coefficient * normalized =
    ∏ i ∈ s.erase exceptional, f i
  product_eq : AddMonoidAlgebra.single 0 coefficient * f exceptional * normalized = ∏ i ∈ s, f i
  error : Laurent K n
  error_eq : error = 1 - AddMonoidAlgebra.single (-maskExponent left) 1 * normalized
  error_positive : ∀ β, error.coeff β ≠ 0 → 0 < termOrder v P.weights β (error.coeff β)
  shifted_error_eq : AddMonoidAlgebra.single (maskExponent left) 1 * error =
    AddMonoidAlgebra.single (maskExponent left) 1 - normalized
  shifted_error_mem : AddMonoidAlgebra.single (maskExponent left) 1 * error ∈
    modelSourceRing v π P Λ

/-- Full Step 1, including the empty complementary product when there is
only one factor. No generic-weight or discreteness hypothesis is needed. -/
theorem modelProduct_shape (v : Valuation K ℝ≥0) (π : K)
    (hπ0 : π ≠ 0) (hπ : realValuationOrder v π = 1) (P : ModelParameters n)
    (hn : 0 < n) (Λ : Finset (Fin n)) {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (f : ι → Laurent K n) (hf : ∀ i ∈ s, f i ∈ modelSourceRing v π P Λ)
    {j : Laurent K n} (hj : j ∈ modelJunk v π P)
    (hprod : (∏ i ∈ s, f i) = endpointMonomial π P.kappa 1 * (1 + j)) :
    Nonempty (ModelProductShape v π P Λ s f) := by
  classical
  obtain ⟨β, i₀, hβ, hexp, hi₀, hji₀, hei₀, hshift, hothers⟩ :=
    modelProduct_unique_exceptional v π hπ0 hπ P hn Λ s f hf hj hprod
  obtain ⟨L, D, hdisj, hpartition, hL, hother_exp, hexceptional_exp⟩ :=
    squarefree_partition_of_exponent_sum s β hi₀ Λ hexp hshift
      (fun i hi hne => (hothers i hi hne).2.2.1)
      (fun i hi hne => (hothers i hi hne).2.2.2)
  let q' : Laurent K n := ∏ i ∈ s.erase i₀, f i
  have hqinit : IsInitialTerm v P.weights q' (maskExponent L) := by
    rw [← hother_exp]
    exact IsInitialTerm.finset_prod _ f β (fun i hi => hβ i (Finset.mem_of_mem_erase hi))
  let c := q'.coeff (maskExponent L)
  have hc : c ≠ 0 := hqinit.1
  have hco : realValuationOrder v c = 0 := by
    dsimp only [c, q']
    rw [← hother_exp, IsInitialTerm.finset_coefficientOrder _ f β
      (fun i hi => hβ i (Finset.mem_of_mem_erase hi))]
    exact Finset.sum_eq_zero (fun i hi => (hothers i (Finset.mem_of_mem_erase hi)
      (Finset.ne_of_mem_erase hi)).1)
  have hq'mem : q' ∈ modelSourceRing v π P Λ :=
    (modelSourceRing v π P Λ).prod_mem (fun i hi => hf i (Finset.mem_of_mem_erase hi))
  let q := AddMonoidAlgebra.single 0 c⁻¹ * q'
  obtain ⟨hqmem, hqinitial, hqcoeff⟩ :=
    modelSourceRing_normalize_initial v π P Λ hq'mem hqinit hco
  have hscaled : AddMonoidAlgebra.single 0 c * q = q' := by
    dsimp only [q]
    rw [← mul_assoc, AddMonoidAlgebra.single_mul_single]
    simp only [zero_add, mul_inv_cancel₀ hc]
    change 1 * q' = q'
    exact one_mul q'
  have hproduct : AddMonoidAlgebra.single 0 c * f i₀ * q = ∏ i ∈ s, f i := by
    calc
      _ = f i₀ * (AddMonoidAlgebra.single 0 c * q) := by ring
      _ = f i₀ * q' := by rw [hscaled]
      _ = ∏ i ∈ s, f i := Finset.mul_prod_erase s f hi₀
  let d := 1 - AddMonoidAlgebra.single (-maskExponent L) 1 * q
  obtain ⟨hdpos, hdeq, hdmem⟩ :=
    modelSourceRing_initial_error v π P Λ L hL hqmem hqinitial hqcoeff
  exact ⟨{
    exceptional := i₀
    exceptional_mem := hi₀
    initialExponent := β
    initial := hβ
    exceptional_initial_junk := hji₀
    exceptional_coefficient_order := hei₀
    other_coefficient_order := fun i hi hne => (hothers i hi hne).1
    left := L
    right := D
    disjoint := hdisj
    partition := hpartition
    left_subset := hL
    other_exponent := hother_exp
    exceptional_exponent := hexceptional_exp
    coefficient := c
    coefficient_eq := rfl
    coefficient_ne_zero := hc
    coefficient_order := hco
    normalized := q
    normalized_eq := rfl
    normalized_mem := hqmem
    normalized_initial := hqinitial
    normalized_coefficient := hqcoeff
    scaled_normalized := hscaled
    product_eq := hproduct
    error := d
    error_eq := rfl
    error_positive := hdpos
    shifted_error_eq := hdeq
    shifted_error_mem := hdmem }⟩

theorem ModelProductShape.shifted_error_term (v : Valuation K ℝ≥0) (π : K)
    (hπ0 : π ≠ 0) (hπ : realValuationOrder v π = 1) (P : ModelParameters n)
    (Λ : Finset (Fin n)) {ι : Type*} [DecidableEq ι] {s : Finset ι}
    {f : ι → Laurent K n} (H : ModelProductShape v π P Λ s f) (β : Fin n → ℤ) :
    AddMonoidAlgebra.single (maskExponent H.left + β) (H.error.coeff β) ∈
      modelSourceRing v π P Λ := by
  have h := H.shifted_error_mem
  change _ ∈ (modelSourceRing v π P Λ).toAddSubgroup at h ⊢
  rw [modelSourceRing_eq_supported v π hπ0 hπ P Λ] at h ⊢
  have hterm := (MonomialClass.mem_supported_iff_single v _ _).mp h
    (maskExponent H.left + β)
  simpa using hterm

theorem ModelProductShape.scaled_exceptional_mem (v : Valuation K ℝ≥0) (π : K)
    (P : ModelParameters n) (Λ : Finset (Fin n)) {ι : Type*} [DecidableEq ι]
    {s : Finset ι} {f : ι → Laurent K n} (H : ModelProductShape v π P Λ s f)
    (hf : f H.exceptional ∈ modelSourceRing v π P Λ) :
    AddMonoidAlgebra.single 0 H.coefficient * f H.exceptional ∈ modelSourceRing v π P Λ := by
  have hc := (realValuationOrder_nonneg_iff v H.coefficient_ne_zero).mp
    (le_of_eq H.coefficient_order.symm)
  exact (modelSourceRing v π P Λ).mul_mem
    (modelPolynomialRing_le_modelSourceRing v π P Λ
      (modelPolynomialRing_constant v Λ _ hc)) hf

theorem ModelProductShape.scaled_exceptional_not_junk (v : Valuation K ℝ≥0) (π : K)
    (P : ModelParameters n) (Λ : Finset (Fin n)) {ι : Type*} [DecidableEq ι]
    {s : Finset ι} {f : ι → Laurent K n} (H : ModelProductShape v π P Λ s f)
    (hf : f H.exceptional ∉ modelJunk v π P) :
    AddMonoidAlgebra.single 0 H.coefficient * f H.exceptional ∉ modelJunk v π P := by
  intro hmem
  apply hf
  have hc : 0 ≤ realValuationOrder v H.coefficient⁻¹ := by
    simp [H.coefficient_order]
  have hconst := modelRing_constant v π P H.coefficient⁻¹
    ((realValuationOrder_nonneg_iff v (inv_ne_zero H.coefficient_ne_zero)).mp hc)
  have h := modelJunk_mul_left v π P hconst hmem
  rw [← mul_assoc, AddMonoidAlgebra.single_mul_single] at h
  simp only [zero_add, inv_mul_cancel₀ H.coefficient_ne_zero] at h
  change 1 * f H.exceptional ∈ modelJunk v π P at h
  simpa using h

/-- The squarefree partition gives the literal monomial identity
Z₁ = Z_N Y_L Y_D used when dividing the product equation in Step 2. -/
theorem endpointMonomial_partition (π : K) (κ : ℕ) (L D : Finset (Fin n))
    (hdisj : Disjoint L D)
    (hpartition : L ∪ D = Finset.univ.filter (fun l => 0 < l.val)) :
    endpointMonomial π κ n * AddMonoidAlgebra.single (maskExponent L) 1 *
      AddMonoidAlgebra.single (maskExponent D) 1 = endpointMonomial π κ 1 := by
  classical
  have hexp : (fun i : Fin n => if i.val < n then (-1 : ℤ) else 0) +
      maskExponent L + maskExponent D = (fun i => if i.val < 1 then -1 else 0) := by
    funext i
    have hmem := congrArg (fun X : Finset (Fin n) => i ∈ X) hpartition
    have htail : (i ∈ L ∨ i ∈ D) ↔ 0 < i.val := by
      simpa only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and] using hmem.to_iff
    have hnot : ¬(i ∈ L ∧ i ∈ D) := fun h => Finset.disjoint_left.mp hdisj h.1 h.2
    simp only [Pi.add_apply, maskExponent, ite_eq_left i.isLt]
    split_ifs <;> simp_all
  simp only [endpointMonomial, AddMonoidAlgebra.single_mul_single, mul_one, hexp]

theorem ModelProductShape.left_weight_bound (v : Valuation K ℝ≥0) (π : K)
    (P : ModelParameters n) (Λ : Finset (Fin n)) {ι : Type*} [DecidableEq ι]
    {s : Finset ι} {f : ι → Laurent K n} (H : ModelProductShape v π P Λ s f)
    (hΛ : 2 * ∑ l ∈ Λ.filter (fun l => 0 < l.val), P.weights l ≤
      remainingValue P.weights P.kappa 1) :
    2 * ∑ l ∈ H.left, P.weights l ≤ remainingValue P.weights P.kappa 1 := by
  have hsubset : H.left ⊆ Λ.filter (fun l => 0 < l.val) := by
    intro l hl
    have htail : l ∈ Finset.univ.filter (fun l => 0 < l.val) := by
      rw [← H.partition]
      exact Finset.mem_union_left _ hl
    exact Finset.mem_filter.mpr ⟨H.left_subset hl, (Finset.mem_filter.mp htail).2⟩
  have hle := Finset.sum_le_sum_of_subset_of_nonneg hsubset
    (fun l _ _ => (P.weights_pos l).le)
  exact (mul_le_mul_of_nonneg_left hle (by norm_num)).trans hΛ

end HereditaryAtomicity.DVRBase
