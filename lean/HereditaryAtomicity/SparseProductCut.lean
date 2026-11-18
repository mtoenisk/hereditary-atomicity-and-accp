import Factorization.Definitions
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.RingTheory.Localization.FractionRing

/-!
# Real orders and actual polynomial cut rings

The finite order is the negative logarithm of a nonnegative-real valuation.
Its value at zero is a harmless convention; every multiplicative or comparison
statement that uses the finite order explicitly excludes zero.
-/

open scoped NNReal

noncomputable section
namespace HereditaryAtomicity

variable {K : Type*} [Field K]

/-- The additive real order of a nonzero element, extended by zero at zero. -/
def realValuationOrder (v : Valuation K ℝ≥0) (x : K) : ℝ :=
  -Real.log (v x : ℝ)

@[simp] theorem realValuationOrder_zero (v : Valuation K ℝ≥0) :
    realValuationOrder v 0 = 0 := by simp [realValuationOrder]

@[simp] theorem realValuationOrder_one (v : Valuation K ℝ≥0) :
    realValuationOrder v 1 = 0 := by simp [realValuationOrder]

@[simp] theorem realValuationOrder_neg (v : Valuation K ℝ≥0) (x : K) :
    realValuationOrder v (-x) = realValuationOrder v x := by
  simp [realValuationOrder, v.map_neg]

theorem realValuationOrder_mul (v : Valuation K ℝ≥0) {x y : K}
    (hx : x ≠ 0) (hy : y ≠ 0) :
    realValuationOrder v (x*y) = realValuationOrder v x + realValuationOrder v y := by
  have hx' : (v x : ℝ) ≠ 0 := by exact_mod_cast (v.ne_zero_iff.mpr hx)
  have hy' : (v y : ℝ) ≠ 0 := by exact_mod_cast (v.ne_zero_iff.mpr hy)
  simp only [realValuationOrder, map_mul, NNReal.coe_mul, Real.log_mul hx' hy']
  ring

@[simp] theorem realValuationOrder_inv (v : Valuation K ℝ≥0) (x : K) :
    realValuationOrder v x⁻¹ = -realValuationOrder v x := by
  simp [realValuationOrder, Real.log_inv]

theorem realValuationOrder_div (v : Valuation K ℝ≥0) {x y : K}
    (hx : x ≠ 0) (hy : y ≠ 0) :
    realValuationOrder v (x/y) = realValuationOrder v x - realValuationOrder v y := by
  rw [div_eq_mul_inv, realValuationOrder_mul v hx (inv_ne_zero hy),
    realValuationOrder_inv, sub_eq_add_neg]

theorem realValuationOrder_pow (v : Valuation K ℝ≥0) (x : K) (n : ℕ) :
    realValuationOrder v (x^n) = n * realValuationOrder v x := by
  simp only [realValuationOrder, map_pow, NNReal.coe_pow, Real.log_pow]
  ring

theorem realValuationOrder_le_iff (v : Valuation K ℝ≥0) {x y : K}
    (hx : x ≠ 0) (hy : y ≠ 0) :
    realValuationOrder v x ≤ realValuationOrder v y ↔ v y ≤ v x := by
  have hx' : 0 < (v x : ℝ) := by exact_mod_cast (pos_iff_ne_zero.mpr (v.ne_zero_iff.mpr hx))
  have hy' : 0 < (v y : ℝ) := by exact_mod_cast (pos_iff_ne_zero.mpr (v.ne_zero_iff.mpr hy))
  simpa only [realValuationOrder, neg_le_neg_iff, NNReal.coe_le_coe] using
    Real.log_le_log_iff hy' hx'

theorem realValuationOrder_lt_iff (v : Valuation K ℝ≥0) {x y : K}
    (hx : x ≠ 0) (hy : y ≠ 0) :
    realValuationOrder v x < realValuationOrder v y ↔ v y < v x := by
  rw [← not_le, realValuationOrder_le_iff v hy hx, not_le]

theorem realValuationOrder_nonneg_iff (v : Valuation K ℝ≥0) {x : K} (hx : x ≠ 0) :
    0 ≤ realValuationOrder v x ↔ v x ≤ 1 := by
  simpa using realValuationOrder_le_iff v one_ne_zero hx

theorem realValuationOrder_pos_iff (v : Valuation K ℝ≥0) {x : K} (hx : x ≠ 0) :
    0 < realValuationOrder v x ↔ v x < 1 := by
  simpa using realValuationOrder_lt_iff v one_ne_zero hx

theorem realValuationOrder_add_eq_min (v : Valuation K ℝ≥0) {x y : K}
    (hx : x ≠ 0) (hy : y ≠ 0)
    (hne : realValuationOrder v x ≠ realValuationOrder v y) :
    x+y ≠ 0 ∧ realValuationOrder v (x+y) =
      min (realValuationOrder v x) (realValuationOrder v y) := by
  have hvne : v x ≠ v y := fun h => hne (by simp [realValuationOrder, h])
  have hsum := v.map_add_of_distinct_val hvne
  have hsum0 : x+y ≠ 0 := by
    intro h
    have : max (v x) (v y) = 0 := by simpa [h] using hsum.symm
    have hx0 : v x = 0 := le_antisymm (this ▸ le_max_left _ _) (zero_le : (0 : ℝ≥0) ≤ v x)
    exact hx (v.zero_iff.mp hx0)
  refine ⟨hsum0, ?_⟩
  rcases lt_or_gt_of_ne hne with hxy | hyx
  · rw [min_eq_left hxy.le]
    have hval := v.map_add_eq_of_lt_left ((realValuationOrder_lt_iff v hx hy).mp hxy)
    simp [realValuationOrder, hval]
  · rw [min_eq_right hyx.le]
    have hval := v.map_add_eq_of_lt_right ((realValuationOrder_lt_iff v hy hx).mp hyx)
    simp [realValuationOrder, hval]

theorem realValuationOrder_le_add (v : Valuation K ℝ≥0) {x y : K} {c : ℝ}
    (hx : x ≠ 0) (hy : y ≠ 0) (hxy : x+y ≠ 0)
    (hcx : c ≤ realValuationOrder v x) (hcy : c ≤ realValuationOrder v y) :
    c ≤ realValuationOrder v (x+y) := by
  rcases le_total (v x) (v y) with h | h
  · have hh : v (x+y) ≤ v y := (v.map_add x y).trans (max_eq_right h).le
    exact hcy.trans ((realValuationOrder_le_iff v hy hxy).mpr hh)
  · have hh : v (x+y) ≤ v x := (v.map_add x y).trans (max_eq_left h).le
    exact hcx.trans ((realValuationOrder_le_iff v hx hxy).mpr hh)

theorem realValuationOrder_lt_add (v : Valuation K ℝ≥0) {x y : K} {c : ℝ}
    (hx : x ≠ 0) (hy : y ≠ 0) (hxy : x+y ≠ 0)
    (hcx : c < realValuationOrder v x) (hcy : c < realValuationOrder v y) :
    c < realValuationOrder v (x+y) := by
  rcases le_total (v x) (v y) with h | h
  · have hh : v (x+y) ≤ v y := (v.map_add x y).trans (max_eq_right h).le
    exact hcy.trans_le ((realValuationOrder_le_iff v hy hxy).mpr hh)
  · have hh : v (x+y) ≤ v x := (v.map_add x y).trans (max_eq_left h).le
    exact hcx.trans_le ((realValuationOrder_le_iff v hx hxy).mpr hh)

/-- The common open valuation tail, as an actual ideal of a ring on which all
branch orders are nonnegative. -/
def realValuationTail {ι : Type*} (v : ι → Valuation K ℝ≥0)
    (B : Subring K) (hB : ∀ (x : B), x ≠ 0 → ∀ i, 0 ≤ realValuationOrder (v i) x)
    (c : ℝ) : Ideal B where
  carrier := {x | x = 0 ∨ ∀ i, c < realValuationOrder (v i) x}
  zero_mem' := Or.inl rfl
  add_mem' := by
    intro x y hx hy
    rcases hx with rfl | hx
    · simpa using hy
    rcases hy with rfl | hy
    · exact Or.inr (by simpa using hx)
    by_cases hxy : x+y = 0
    · exact Or.inl hxy
    right
    intro i
    by_cases hx0 : x = 0
    · simpa [hx0] using hy i
    by_cases hy0 : y = 0
    · simpa [hy0] using hx i
    exact realValuationOrder_lt_add (v i)
      (Subtype.coe_ne_coe.mpr hx0) (Subtype.coe_ne_coe.mpr hy0)
      (Subtype.coe_ne_coe.mpr hxy) (hx i) (hy i)
  smul_mem' := by
    intro a x hx
    rcases hx with rfl | hx
    · exact Or.inl (mul_zero a)
    by_cases ha : a = 0
    · exact Or.inl (by simp [ha])
    by_cases hx0 : x = 0
    · exact Or.inl (by simp [hx0])
    right
    intro i
    change c < realValuationOrder (v i) ((a : K)*(x : K))
    rw [realValuationOrder_mul (v i) (Subtype.coe_ne_coe.mpr ha)
      (Subtype.coe_ne_coe.mpr hx0)]
    exact lt_of_lt_of_le (hx i) (le_add_of_nonneg_left (hB a ha i))

@[simp] theorem mem_realValuationTail {ι : Type*} (v : ι → Valuation K ℝ≥0)
    (B : Subring K) (hB : ∀ (x : B), x ≠ 0 → ∀ i, 0 ≤ realValuationOrder (v i) x)
    (c : ℝ) (x : B) :
    x ∈ realValuationTail v B hB c ↔ x = 0 ∨ ∀ i, c < realValuationOrder (v i) x :=
  Iff.rfl

/-- A literal sum of a subring and an ideal in the same ambient ring. -/
def subringPlusIdeal {R : Type*} [CommRing R] (P : Subring R) (I : Ideal R) : Subring R where
  carrier := {x | ∃ a ∈ P, ∃ b ∈ I, x = a+b}
  zero_mem' := ⟨0, P.zero_mem, 0, I.zero_mem, by simp⟩
  one_mem' := ⟨1, P.one_mem, 0, I.zero_mem, by simp⟩
  neg_mem' := by
    rintro x ⟨a, ha, b, hb, rfl⟩
    exact ⟨-a, P.neg_mem ha, -b, I.neg_mem hb, neg_add a b⟩
  add_mem' := by
    rintro x y ⟨a, ha, b, hb, rfl⟩ ⟨c, hc, d, hd, rfl⟩
    exact ⟨a+c, P.add_mem ha hc, b+d, I.add_mem hb hd, by ring⟩
  mul_mem' := by
    rintro x y ⟨a, ha, b, hb, rfl⟩ ⟨c, hc, d, hd, rfl⟩
    refine ⟨a*c, P.mul_mem ha hc, a*d+b*c+b*d, ?_, by ring⟩
    exact I.add_mem (I.add_mem (I.mul_mem_left a hd) (I.mul_mem_right c hb))
      (I.mul_mem_left b hd)

@[simp] theorem mem_subringPlusIdeal {R : Type*} [CommRing R] (P : Subring R)
    (I : Ideal R) (x : R) :
    x ∈ subringPlusIdeal P I ↔ ∃ a ∈ P, ∃ b ∈ I, x=a+b := Iff.rfl

theorem subring_le_subringPlusIdeal {R : Type*} [CommRing R] (P : Subring R)
    (I : Ideal R) : P ≤ subringPlusIdeal P I := by
  intro x hx
  exact ⟨x, hx, 0, I.zero_mem, by simp⟩

theorem ideal_subset_subringPlusIdeal {R : Type*} [CommRing R] (P : Subring R)
    (I : Ideal R) : (I : Set R) ⊆ subringPlusIdeal P I := by
  intro x hx
  exact ⟨0, P.zero_mem, x, hx, by simp⟩

theorem realValuationOrder_eq_zero_of_isUnit (v : Valuation K ℝ≥0)
    (B : Subring K) (hB : ∀ (x : B), x ≠ 0 → 0 ≤ realValuationOrder v x)
    {x : B} (hx : IsUnit x) : realValuationOrder v x = 0 := by
  obtain ⟨u, rfl⟩ := hx
  have hmul := realValuationOrder_mul v
    (Subtype.coe_ne_coe.mpr u.ne_zero) (Subtype.coe_ne_coe.mpr u⁻¹.ne_zero)
  have heq : ((u : B) : K) * ((↑u⁻¹ : B) : K) = 1 := by
    exact_mod_cast u.val_inv
  rw [heq, realValuationOrder_one] at hmul
  have hpos := hB u u.ne_zero
  have hpos' := hB (↑(u⁻¹) : B) u⁻¹.ne_zero
  linarith

theorem not_isUnit_of_realValuationOrder_pos (v : Valuation K ℝ≥0)
    (B : Subring K) (hB : ∀ (x : B), x ≠ 0 → 0 ≤ realValuationOrder v x)
    {x : B} (hx : 0 < realValuationOrder v x) : ¬ IsUnit x := by
  intro hu
  exact (ne_of_gt hx) (realValuationOrder_eq_zero_of_isUnit v B hB hu)

/-- Additive atom-value budgets obstruct an actual finite irreducible
factorization. Units are measured intrinsically in the source ring. -/
theorem not_isAtomicDomain_of_atomOrders {R : Type*} [CommRing R] [IsDomain R]
    (o : R → ℝ) (M : AddSubmonoid ℝ) (h1 : o 1 = 0)
    (hmul : ∀ x y, x ≠ 0 → y ≠ 0 → o (x*y)=o x+o y)
    (hu : ∀ x, IsUnit x → o x=0)
    (hirr : ∀ x, Irreducible x → o x ∈ M)
    (x : R) (hx : x ≠ 0) (hxm : o x ∉ M) : ¬ Factorization.IsAtomicDomain R := by
  intro hA
  obtain ⟨s, hs, u, hprod⟩ := hA x hx
  have hval : o s.prod ∈ M := by
    clear hprod
    induction s using Multiset.induction_on with
    | empty => simp [h1]
    | @cons a s ih =>
      have ha := hs a (Multiset.mem_cons_self _ _)
      have hs' : ∀ b ∈ s, Irreducible b := fun b hb => hs b (Multiset.mem_cons_of_mem hb)
      have hsp : s.prod ≠ 0 := Multiset.prod_ne_zero (by
        intro hz
        exact (hs' 0 hz).ne_zero rfl)
      rw [Multiset.prod_cons, hmul a s.prod ha.ne_zero hsp]
      exact M.add_mem (hirr a ha) (ih hs')
  have hsp : s.prod ≠ 0 := by
    intro hz
    apply hx
    rw [← hprod, hz, zero_mul]
  have hvalx : o x = o s.prod := by
    rw [← hprod, hmul s.prod u hsp u.ne_zero, hu u u.isUnit, add_zero]
  exact hxm (hvalx ▸ hval)

theorem realValuationOrder_prod (v : Valuation K ℝ≥0) {α : Type*}
    (s : Finset α) (f : α → K) (hf : ∀ i ∈ s, f i ≠ 0) :
    realValuationOrder v (∏ i ∈ s, f i) = ∑ i ∈ s, realValuationOrder v (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha,
      realValuationOrder_mul v (hf a (Finset.mem_insert_self _ _))
        (Finset.prod_ne_zero_iff.mpr (fun i hi => hf i (Finset.mem_insert_of_mem hi))),
      ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))]

theorem realValuationOrder_sum_eq_of_unique_min (v : Valuation K ℝ≥0)
    {α : Type*} [DecidableEq α] (s : Finset α) (f : α → K)
    (hf : ∀ i ∈ s, f i ≠ 0) {j : α} (hj : j ∈ s)
    (hmin : ∀ i ∈ s, i ≠ j → realValuationOrder v (f j) < realValuationOrder v (f i)) :
    (∑ i ∈ s, f i) ≠ 0 ∧
      realValuationOrder v (∑ i ∈ s, f i) = realValuationOrder v (f j) := by
  have heq : v (∑ i ∈ s, f i) = v (f j) := by
    apply v.map_sum_eq_of_lt hj
    intro i hi
    have his := (Finset.mem_sdiff.mp hi).1
    have hij : i ≠ j := by simpa using (Finset.mem_sdiff.mp hi).2
    exact (realValuationOrder_lt_iff v (hf j hj) (hf i his)).mp (hmin i his hij)
  refine ⟨?_, by simp only [realValuationOrder, heq]⟩
  intro hz
  have : v (f j) = 0 := by simpa [hz] using heq.symm
  exact hf j hj (v.zero_iff.mp this)

/-- A subring containing a nonzero ideal of a domain has the domain's actual
fraction field. Numerators and denominators are both multiplied by one fixed
nonzero common-ideal element. -/
theorem isFractionRing_of_common_nonzeroIdeal (B C : Subring K)
    [IsFractionRing B K] (I : Ideal B) (hne : I ≠ ⊥)
    (hIC : ∀ z : B, z ∈ I → (z : K) ∈ C) : IsFractionRing C K := by
  obtain ⟨z, hzI, hz0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hzK : (z : K) ≠ 0 := Subtype.coe_ne_coe.mpr hz0
  apply IsFractionRing.of_field
  intro x
  obtain ⟨a, b, _, rfl⟩ := IsFractionRing.div_surjective B x
  refine ⟨⟨((a*z : B) : K), hIC (a*z) (I.mul_mem_left a hzI)⟩,
    ⟨((b*z : B) : K), hIC (b*z) (I.mul_mem_left b hzI)⟩, ?_⟩
  change (a : K)/(b : K) = ((a : K)*(z : K))/((b : K)*(z : K))
  exact (mul_div_mul_right (a : K) (b : K) hzK).symm

end HereditaryAtomicity
