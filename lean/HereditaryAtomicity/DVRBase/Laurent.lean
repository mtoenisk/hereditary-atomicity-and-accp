import HereditaryAtomicity.SparseProductCut
import Mathlib.Algebra.MonoidAlgebra.Basic

/-!
# Finite Laurent polynomials and valuation-defined support classes

Exponent coordinates run from zero to n−1, corresponding to the manuscript variables 1
through n. Coefficients are collected before testing valuations. The finite-order
estimates apply to nonzero coefficients.
-/

noncomputable section
namespace HereditaryAtomicity.DVRBase

open scoped BigOperators NNReal

/-- Actual Laurent polynomials in finitely many invertible variables. -/
abbrev Laurent (K : Type*) [Semiring K] (n : ℕ) :=
  AddMonoidAlgebra K (Fin n → ℤ)

variable {K : Type*} [Field K] {n : ℕ}

/-- The finite additive order of a nonzero Laurent term. At a zero coefficient
the value is merely a convention, never a substitute for infinite order. -/
def termOrder (v : Valuation K ℝ≥0) (u : Fin n → ℝ)
    (β : Fin n → ℤ) (c : K) : ℝ :=
  realValuationOrder v c + ∑ i, (β i : ℝ) * u i

@[simp] theorem termOrder_neg (v : Valuation K ℝ≥0) (u : Fin n → ℝ)
    (β : Fin n → ℤ) (c : K) : termOrder v u β (-c) = termOrder v u β c := by
  simp [termOrder]

theorem termOrder_mul (v : Valuation K ℝ≥0) (u : Fin n → ℝ)
    (β γ : Fin n → ℤ) {c d : K} (hc : c ≠ 0) (hd : d ≠ 0) :
    termOrder v u (β + γ) (c * d) = termOrder v u β c + termOrder v u γ d := by
  simp only [termOrder, realValuationOrder_mul v hc hd, Pi.add_apply,
    Int.cast_add, add_mul, Finset.sum_add_distrib]
  ring

/-- The additive ultrametric inequality with the nonzero hypotheses needed by
the finite real-order convention. -/
theorem realOrder_add_ge_min (v : Valuation K ℝ≥0) {a b : K}
    (ha : a ≠ 0) (hb : b ≠ 0) (hab : a + b ≠ 0) :
    min (realValuationOrder v a) (realValuationOrder v b) ≤
      realValuationOrder v (a + b) := by
  rcases le_total (realValuationOrder v a) (realValuationOrder v b) with h | h
  · rw [min_eq_left h]
    apply (realValuationOrder_le_iff v ha hab).mpr
    exact (v.map_add a b).trans (max_le le_rfl ((realValuationOrder_le_iff v ha hb).mp h))
  · rw [min_eq_right h]
    apply (realValuationOrder_le_iff v hb hab).mpr
    exact (v.map_add a b).trans (max_le ((realValuationOrder_le_iff v hb ha).mp h) le_rfl)

/-- A class of monomials whose membership depends only on the exponent and
coefficient order, and survives increasing the coefficient order. -/
structure MonomialClass (n : ℕ) where
  contains : (Fin n → ℤ) → ℝ → Prop
  upward : ∀ β {a b : ℝ}, a ≤ b → contains β a → contains β b

namespace MonomialClass

variable (v : Valuation K ℝ≥0) (M : MonomialClass n)

/-- The allowed coefficients at a fixed exponent, with zero included. -/
def coefficients (β : Fin n → ℤ) : AddSubgroup K where
  carrier := {c | c = 0 ∨ M.contains β (realValuationOrder v c)}
  zero_mem' := Or.inl rfl
  add_mem' := by
    intro a b ha hb
    rcases ha with rfl | ha
    · simpa using hb
    rcases hb with rfl | hb
    · simpa using Or.inr ha
    by_cases hab : a + b = 0
    · exact Or.inl hab
    by_cases ha0 : a = 0
    · simpa [ha0] using Or.inr hb
    by_cases hb0 : b = 0
    · simpa [hb0] using Or.inr ha
    right
    have hmin : M.contains β (min (realValuationOrder v a) (realValuationOrder v b)) := by
      rcases le_total (realValuationOrder v a) (realValuationOrder v b) with h | h
      · simpa [min_eq_left h] using ha
      · simpa [min_eq_right h] using hb
    exact M.upward β (realOrder_add_ge_min v ha0 hb0 hab) hmin
  neg_mem' := by
    intro a ha
    rcases ha with rfl | ha
    · exact Or.inl (neg_zero)
    · exact Or.inr (by simpa using ha)

@[simp] theorem mem_coefficients {β : Fin n → ℤ} {c : K} :
    c ∈ M.coefficients v β ↔ c = 0 ∨ M.contains β (realValuationOrder v c) := Iff.rfl

/-- Laurent polynomials all of whose nonzero terms lie in a monomial class. -/
def supported : AddSubgroup (Laurent K n) where
  carrier := {f | ∀ β, f.coeff β ∈ M.coefficients v β}
  zero_mem' := by intro β; simp
  add_mem' := by
    intro f g hf hg β
    simpa using (M.coefficients v β).add_mem (hf β) (hg β)
  neg_mem' := by
    intro f hf β
    simpa using (M.coefficients v β).neg_mem (hf β)

@[simp] theorem mem_supported {f : Laurent K n} :
    f ∈ M.supported v ↔ ∀ β, f.coeff β ≠ 0 →
      M.contains β (realValuationOrder v (f.coeff β)) := by
  constructor
  · intro h β hβ
    exact (h β).resolve_left hβ
  · intro h β
    by_cases hβ : f.coeff β = 0
    · exact Or.inl hβ
    · exact Or.inr (h β hβ)

theorem single_mem_supported (β : Fin n → ℤ) (c : K) :
    AddMonoidAlgebra.single β c ∈ M.supported v ↔
      c = 0 ∨ M.contains β (realValuationOrder v c) := by
  classical
  constructor
  · intro h
    simpa using h β
  · intro h γ
    by_cases hγ : β = γ
    · subst γ; simpa using h
    · simp [hγ]

/-- Membership is termwise, using the actual collected coefficient. -/
theorem mem_supported_iff_single (f : Laurent K n) :
    f ∈ M.supported v ↔ ∀ β,
      AddMonoidAlgebra.single β (f.coeff β) ∈ M.supported v := by
  simp only [single_mem_supported]
  rfl

/-- Pointwise union of two upward closed monomial classes. -/
def union (N : MonomialClass n) : MonomialClass n where
  contains β e := M.contains β e ∨ N.contains β e
  upward := by
    intro β a b h
    exact Or.imp (M.upward β h) (N.upward β h)

@[simp] theorem union_contains (N : MonomialClass n) (β : Fin n → ℤ) (e : ℝ) :
    (M.union N).contains β e ↔ M.contains β e ∨ N.contains β e := Iff.rfl

theorem supported_mono {N : MonomialClass n}
    (h : ∀ β e, M.contains β e → N.contains β e) :
    M.supported v ≤ N.supported v := by
  intro f hf
  rw [mem_supported] at hf ⊢
  exact fun β hβ => h β _ (hf β hβ)

/-- Taking the union of upward closed monomial classes corresponds exactly to
adding their additive groups of supported polynomials. -/
theorem supported_union (N : MonomialClass n) :
    (M.union N).supported v = M.supported v ⊔ N.supported v := by
  classical
  apply le_antisymm
  · intro f hf
    rw [← AddMonoidAlgebra.sum_coeff_single f, Finsupp.sum]
    apply AddSubgroup.sum_mem
    intro β hβ
    have h := (mem_supported v (M.union N)).mp hf β (Finsupp.mem_support_iff.mp hβ)
    rcases h with h | h
    · exact AddSubgroup.mem_sup_left ((single_mem_supported v M β _).mpr (Or.inr h))
    · exact AddSubgroup.mem_sup_right ((single_mem_supported v N β _).mpr (Or.inr h))
  · apply sup_le
    · exact supported_mono v M fun _ _ h => Or.inl h
    · exact supported_mono v N fun _ _ h => Or.inr h

/-- Multiplicative closure of monomials, together with the constant monomial 1. -/
structure IsMultiplicative : Prop where
  one_mem : M.contains 0 0
  add_mem : ∀ {β γ : Fin n → ℤ} {e f : ℝ},
    M.contains β e → M.contains γ f → M.contains (β + γ) (e + f)

theorem coefficients_mul (hM : M.IsMultiplicative)
    {β γ : Fin n → ℤ} {a b : K}
    (ha : a ∈ M.coefficients v β) (hb : b ∈ M.coefficients v γ) :
    a * b ∈ M.coefficients v (β + γ) := by
  by_cases ha0 : a = 0
  · simp [ha0]
  by_cases hb0 : b = 0
  · simp [hb0]
  apply Or.inr
  rw [realValuationOrder_mul v ha0 hb0]
  exact hM.add_mem (ha.resolve_left ha0) (hb.resolve_left hb0)

theorem mul_mem_supported (hM : M.IsMultiplicative)
    {f g : Laurent K n} (hf : f ∈ M.supported v) (hg : g ∈ M.supported v) :
    f * g ∈ M.supported v := by
  classical
  intro β
  rw [AddMonoidAlgebra.coeff_mul, Finsupp.sum]
  apply AddSubgroup.sum_mem
  intro γ hγ
  rw [Finsupp.sum]
  apply AddSubgroup.sum_mem
  intro δ hδ
  split_ifs with h
  · rw [← h]
    exact coefficients_mul v M hM (hf γ) (hg δ)
  · exact (M.coefficients v β).zero_mem

/-- The actual subring associated with a multiplicatively closed support class. -/
def supportedSubring (hM : M.IsMultiplicative) : Subring (Laurent K n) where
  toAddSubgroup := M.supported v
  one_mem' := by
    change AddMonoidAlgebra.single 0 1 ∈ M.supported v
    exact (single_mem_supported v M 0 1).mpr (Or.inr (by simpa using hM.one_mem))
  mul_mem' := mul_mem_supported v M hM

@[simp] theorem mem_supportedSubring (hM : M.IsMultiplicative) (f : Laurent K n) :
    f ∈ M.supportedSubring v hM ↔ f ∈ M.supported v := Iff.rfl

/-- Translation by a nonzero monomial of exponent β and coefficient order e. -/
def translate (β : Fin n → ℤ) (e : ℝ) : MonomialClass n where
  contains γ f := M.contains (-β + γ) (f - e)
  upward := by
    intro γ a b h
    exact M.upward _ (sub_le_sub_right h e)

@[simp] theorem translate_contains (β γ : Fin n → ℤ) (e f : ℝ) :
    (M.translate β e).contains γ f ↔ M.contains (-β + γ) (f - e) := Iff.rfl

/-- Multiplication by a nonzero monomial translates the literal support class. -/
theorem single_mul_mem_translate_iff (β : Fin n → ℤ) {c : K} (hc : c ≠ 0)
    (f : Laurent K n) :
    AddMonoidAlgebra.single β c * f ∈
        (M.translate β (realValuationOrder v c)).supported v ↔ f ∈ M.supported v := by
  constructor
  · intro h
    rw [mem_supported] at h ⊢
    intro γ hγ
    have hprod : (AddMonoidAlgebra.single β c * f).coeff (β + γ) ≠ 0 := by
      simpa using mul_ne_zero hc hγ
    have hh := h (β + γ) hprod
    simpa [translate, realValuationOrder_mul v hc hγ] using hh
  · intro h
    rw [mem_supported] at h ⊢
    intro γ hγ
    have hf : f.coeff (-β + γ) ≠ 0 := by
      intro hf
      simp [AddMonoidAlgebra.coeff_single_mul_apply, hf] at hγ
    simpa [translate, AddMonoidAlgebra.coeff_single_mul_apply,
      realValuationOrder_mul v hc hf] using h (-β + γ) hf

/-- The translated support group consists exactly of actual monomial multiples. -/
theorem mem_translate_iff_exists (β : Fin n → ℤ) {c : K} (hc : c ≠ 0)
    (f : Laurent K n) :
    f ∈ (M.translate β (realValuationOrder v c)).supported v ↔
      ∃ g ∈ M.supported v, AddMonoidAlgebra.single β c * g = f := by
  constructor
  · intro hf
    let g : Laurent K n := AddMonoidAlgebra.single (-β) c⁻¹ * f
    have hg : AddMonoidAlgebra.single β c * g = f := by
      simp only [g, ← mul_assoc, AddMonoidAlgebra.single_mul_single,
        add_neg_cancel, mul_inv_cancel₀ hc]
      exact one_mul f
    refine ⟨g, ?_, hg⟩
    exact (single_mul_mem_translate_iff v M β hc g).mp (hg.symm ▸ hf)
  · rintro ⟨g, hg, rfl⟩
    exact (single_mul_mem_translate_iff v M β hc g).mpr hg

/-- A supported subring is generated by its actual allowed single monomials. -/
theorem closure_singles_eq_supportedSubring (hM : M.IsMultiplicative) :
    Subring.closure {f : Laurent K n | ∃ β c,
      (c = 0 ∨ M.contains β (realValuationOrder v c)) ∧
        f = AddMonoidAlgebra.single β c} = M.supportedSubring v hM := by
  classical
  apply le_antisymm
  · apply Subring.closure_le.mpr
    rintro f ⟨β, c, hc, rfl⟩
    exact (single_mem_supported v M β c).mpr hc
  · intro f hf
    rw [← AddMonoidAlgebra.sum_coeff_single f, Finsupp.sum]
    apply Subring.sum_mem
    intro β _
    apply Subring.subset_closure
    exact ⟨β, f.coeff β, hf β, rfl⟩

end MonomialClass

/-- Evaluate one exponent at a tuple of nonzero elements. -/
def monomial (y : Fin n → Kˣ) : Multiplicative (Fin n → ℤ) →* K where
  toFun β := ((∏ i, y i ^ β.toAdd i : Kˣ) : K)
  map_one' := by simp
  map_mul' β γ := by
    change ((∏ i, y i ^ (β.toAdd i + γ.toAdd i) : Kˣ) : K) = _
    simp only [zpow_add, Finset.prod_mul_distrib, Units.val_mul]

@[simp] theorem monomial_ne_zero (y : Fin n → Kˣ) (β : Fin n → ℤ) :
    monomial y (.ofAdd β) ≠ 0 := Units.ne_zero _

/-- The actual evaluation homomorphism, allowing an embedded coefficient ring. -/
def eval {A : Type*} [CommRing A] (f : A →+* K) (y : Fin n → Kˣ) :
    Laurent A n →+* K :=
  AddMonoidAlgebra.liftNCRingHom f (monomial y) (fun _ _ => Commute.all _ _)

@[simp] theorem eval_single {A : Type*} [CommRing A] (f : A →+* K)
    (y : Fin n → Kˣ) (β : Fin n → ℤ) (c : A) :
    eval f y (AddMonoidAlgebra.single β c) = f c * monomial y (.ofAdd β) := by
  simp [eval]

theorem eval_eq_sum {A : Type*} [CommRing A] (f : A →+* K)
    (y : Fin n → Kˣ) (p : Laurent A n) :
    eval f y p = ∑ β ∈ p.coeff.support, f (p.coeff β) * monomial y (.ofAdd β) := by
  conv_lhs => rw [← AddMonoidAlgebra.sum_coeff_single p]
  simp [Finsupp.sum]

/-- One of the literal Laurent variables. -/
def variableMonomial (i : Fin n) : Laurent K n := AddMonoidAlgebra.single (Pi.single i 1) 1

theorem prod_variable_pow (m : Fin n → ℕ) :
    (∏ i, (variableMonomial i : Laurent K n) ^ m i) =
      AddMonoidAlgebra.single (fun i => (m i : ℤ)) 1 := by
  classical
  simp only [variableMonomial, AddMonoidAlgebra.single_pow, one_pow,
    AddMonoidAlgebra.prod_single, Finset.prod_const_one]
  congr 1
  funext j
  simp only [Finset.sum_apply, nsmul_eq_mul]
  rw [Finset.sum_eq_single j]
  · simp
  · intro i _ hij
    simp [Pi.single_eq_of_ne (Ne.symm hij)]
  · simp

/-- A subring containing all variables contains every nonnegative monomial
whose constant coefficient it contains. -/
theorem single_nonneg_mem_subring (S : Subring (Laurent K n))
    (hvar : ∀ i, variableMonomial i ∈ S) (β : Fin n → ℤ) (hβ : ∀ i, 0 ≤ β i)
    (c : K) (hc : AddMonoidAlgebra.single 0 c ∈ S) :
    AddMonoidAlgebra.single β c ∈ S := by
  have hm : (∏ i, (variableMonomial i : Laurent K n) ^ (β i).toNat) ∈ S :=
    S.prod_mem fun i _ => S.pow_mem (hvar i) _
  rw [prod_variable_pow] at hm
  have he : (fun i => ((β i).toNat : ℤ)) = β := by
    funext i
    exact Int.toNat_of_nonneg (hβ i)
  rw [he] at hm
  simpa only [AddMonoidAlgebra.single_mul_single, zero_add, mul_one] using S.mul_mem hc hm

end HereditaryAtomicity.DVRBase
