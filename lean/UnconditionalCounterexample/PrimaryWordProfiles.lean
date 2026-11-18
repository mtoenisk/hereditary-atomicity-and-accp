import UnconditionalCounterexample.PrincipalProfiles
import UnconditionalCounterexample.NormalizedWords
import UnconditionalCounterexample.StageExponents
import Mathlib.Algebra.Order.GroupWithZero.WithZero

/-!
# Actual primary profiles of signed normalized words

The valuation of the literal finite signed product is computed and connected to
`NormalizedWords.Represents`. The prescribed b/q generator valuations remain explicit
inputs, supplied by the simultaneous construction.
-/

noncomputable section
namespace UnconditionalCounterexample.PrimaryWordProfiles
open WithZero NormalizedWords PrincipalProfiles
open scoped BigOperators
variable {α K : Type*} [Field K]

/-- The prescribed primary profile of b_n in the exponent-three construction. -/
def bWeight (n j : ℕ) : ℤ := if j = 2 * n then 3 else 0

/-- The prescribed primary profile of q_n in the two-coordinate construction. -/
def qWeight (n j : ℕ) : ℤ :=
  (if j = 2 * n then 2 else 0) + (if j = 2 * n + 1 then 1 else 0) +
    (if j = 2 * n + 2 then 2 else 0)

theorem prod_exp_neg (s : Finset α) (a : α → ℤ) :
    (∏ i ∈ s, exp (-(a i))) = exp (-(∑ i ∈ s, a i)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi, ih, neg_add, exp_add]

/-- Evaluate the literal finite signed product using the actual valuation. -/
theorem valuation_word (v : Valuation K ℤᵐ⁰) (W : α → K) (a : α → ℤ)
    (ha : ∀ i, v (W i) = exp (-(a i))) (e : α →₀ ℤ) :
    v (word W e) = exp (-(e.sum (fun i z => z * a i))) := by
  classical
  rw [word, Finsupp.prod, map_prod]
  calc
    (∏ i ∈ e.support, v (W i ^ e i)) =
        ∏ i ∈ e.support, exp (-(e i * a i)) := by
      apply Finset.prod_congr rfl
      intro i _
      rw [map_zpow₀, ha, ← exp_zsmul]
      congr 1
      simp only [zsmul_eq_mul, mul_neg, Int.cast_id]
    _ = _ := prod_exp_neg e.support (fun i => e i * a i)

/-- A sparse profile reads the coefficient at its one supporting stage. -/
theorem sum_indicator (e : ℕ →₀ ℤ) (i : ℕ) (a : ℤ) :
    e.sum (fun j z => z * (if j = i then a else 0)) = e i * a := by
  classical
  simp only [mul_ite, mul_zero]
  rw [Finsupp.sum_ite_eq']
  split_ifs with hi
  · rfl
  · rw [Finsupp.notMem_support_iff.mp hi, zero_mul]

/-- Sparse row formulas for the actual generator valuations imply the required
primary representation of every literal signed normalized word. -/
theorem represents_of_row_profiles (v : ℕ → Valuation K ℤᵐ⁰) (W : ℕ → K)
    (hzero : ∀ i, v 0 (W i) = exp (-((if i = (Generator.b 0).stage then 3 else 0) +
      (if i = (Generator.q 0).stage then 2 else 0))))
    (hodd : ∀ n i, v (2 * n + 1) (W i) =
      exp (-(if i = (Generator.q n).stage then 1 else 0)))
    (heven : ∀ n i, v (2 * n + 2) (W i) =
      exp (-((if i = (Generator.b (n + 1)).stage then 3 else 0) +
        (if i = (Generator.q (n + 1)).stage then 2 else 0) +
        (if i = (Generator.q n).stage then 2 else 0))))
    (e : ℕ →₀ ℤ) (x : K) (g : ℕ → ℤ)
    (hx : x = word W e ∨ x = -word W e) (hg : ∀ j, v j x = exp (-(g j))) :
    Represents (StageExponents.bExponents e) (StageExponents.qExponents e) g := by
  have hw (j : ℕ) : v j (word W e) = exp (-(g j)) := by
    rcases hx with hx | hx
    · simpa only [hx] using hg j
    · simpa only [hx, Valuation.map_neg] using hg j
  constructor
  · have h := neg_injective (exp_injective ((hw 0).symm.trans
      (valuation_word (v 0) W _ hzero e)))
    simp only [Finsupp.sum, mul_add, Finset.sum_add_distrib] at h
    change g 0 = e.sum (fun i z => z * (if i = (Generator.b 0).stage then 3 else 0)) +
      e.sum (fun i z => z * (if i = (Generator.q 0).stage then 2 else 0)) at h
    rw [sum_indicator, sum_indicator] at h
    change g 0 = 3 * e (Generator.b 0).stage + 2 * e (Generator.q 0).stage
    linarith
  · intro n
    have h := neg_injective (exp_injective ((hw (2 * n + 1)).symm.trans
      (valuation_word (v (2 * n + 1)) W _ (hodd n) e)))
    rw [sum_indicator, mul_one] at h
    exact h
  · intro n
    have h := neg_injective (exp_injective ((hw (2 * n + 2)).symm.trans
      (valuation_word (v (2 * n + 2)) W _ (heven n) e)))
    simp only [Finsupp.sum, mul_add, Finset.sum_add_distrib] at h
    change g (2 * n + 2) =
      e.sum (fun i z => z * (if i = (Generator.b (n + 1)).stage then 3 else 0)) +
      e.sum (fun i z => z * (if i = (Generator.q (n + 1)).stage then 2 else 0)) +
      e.sum (fun i z => z * (if i = (Generator.q n).stage then 2 else 0)) at h
    rw [sum_indicator, sum_indicator, sum_indicator] at h
    change g (2 * n + 2) = 3 * e (Generator.b (n + 1)).stage +
      2 * e (Generator.q (n + 1)).stage + 2 * e (Generator.q n).stage
    linarith

/-- Column profiles of the actual b and q generators give the sparse primary rows. -/
theorem row_profiles_of_bq (v : ℕ → Valuation K ℤᵐ⁰) (W : ℕ → K)
    (hb : ∀ n j, v j (W (Generator.b n).stage) = exp (-(bWeight n j)))
    (hq : ∀ n j, v j (W (Generator.q n).stage) = exp (-(qWeight n j))) :
    (∀ i, v 0 (W i) = exp (-((if i = (Generator.b 0).stage then 3 else 0) +
      (if i = (Generator.q 0).stage then 2 else 0)))) ∧
    (∀ n i, v (2 * n + 1) (W i) =
      exp (-(if i = (Generator.q n).stage then 1 else 0))) ∧
    (∀ n i, v (2 * n + 2) (W i) =
      exp (-((if i = (Generator.b (n + 1)).stage then 3 else 0) +
        (if i = (Generator.q (n + 1)).stage then 2 else 0) +
        (if i = (Generator.q n).stage then 2 else 0)))) := by
  constructor
  · intro i
    obtain ⟨a, rfl⟩ := StageExponents.stage_surjective i
    cases a with
    | b m =>
      rw [hb]
      apply congrArg (fun z : ℤ => exp (-z))
      simp only [bWeight, StageExponents.stage_injective.eq_iff,
        Generator.b.injEq, reduceCtorEq, ite_false, add_zero]
      split_ifs <;> omega
    | q m =>
      rw [hq]
      apply congrArg (fun z : ℤ => exp (-z))
      simp only [qWeight, StageExponents.stage_injective.eq_iff,
        Generator.q.injEq, reduceCtorEq, ite_false, zero_add]
      split_ifs <;> omega
  constructor
  · intro n i
    obtain ⟨a, rfl⟩ := StageExponents.stage_surjective i
    cases a with
    | b m =>
      rw [hb]
      apply congrArg (fun z : ℤ => exp (-z))
      simp only [bWeight, StageExponents.stage_injective.eq_iff, reduceCtorEq, ite_false]
      split_ifs <;> omega
    | q m =>
      rw [hq]
      apply congrArg (fun z : ℤ => exp (-z))
      simp only [qWeight, StageExponents.stage_injective.eq_iff, Generator.q.injEq]
      split_ifs <;> omega
  · intro n i
    obtain ⟨a, rfl⟩ := StageExponents.stage_surjective i
    cases a with
    | b m =>
      rw [hb]
      apply congrArg (fun z : ℤ => exp (-z))
      simp only [bWeight, StageExponents.stage_injective.eq_iff,
        Generator.b.injEq, reduceCtorEq, ite_false, add_zero]
      split_ifs <;> omega
    | q m =>
      rw [hq]
      apply congrArg (fun z : ℤ => exp (-z))
      simp only [qWeight, StageExponents.stage_injective.eq_iff,
        Generator.q.injEq, reduceCtorEq, ite_false, zero_add]
      split_ifs <;> omega

/-- The actual signed normalized product satisfies the abstract primary-profile
representation solely from the prescribed valuations of its b/q generators. -/
theorem represents_of_generator_profiles (v : ℕ → Valuation K ℤᵐ⁰) (W : ℕ → K)
    (hb : ∀ n j, v j (W (Generator.b n).stage) = exp (-(bWeight n j)))
    (hq : ∀ n j, v j (W (Generator.q n).stage) = exp (-(qWeight n j)))
    (e : ℕ →₀ ℤ) (x : K) (g : ℕ → ℤ)
    (hx : x = word W e ∨ x = -word W e) (hg : ∀ j, v j x = exp (-(g j))) :
    Represents (StageExponents.bExponents e) (StageExponents.qExponents e) g := by
  obtain ⟨hzero, hodd, heven⟩ := row_profiles_of_bq v W hb hq
  exact represents_of_row_profiles v W hzero hodd heven e x g hx hg

/-- The canonical additive order is the negative logarithm of the actual
multiplicative primary valuation. -/
theorem represents_actual_primary_orders (v : ℕ → Valuation K ℤᵐ⁰) (W : ℕ → K)
    (hb : ∀ n j, v j (W (Generator.b n).stage) = exp (-(bWeight n j)))
    (hq : ∀ n j, v j (W (Generator.q n).stage) = exp (-(qWeight n j)))
    (e : ℕ →₀ ℤ) (x : K) (hx0 : x ≠ 0)
    (hx : x = word W e ∨ x = -word W e) :
    Represents (StageExponents.bExponents e) (StageExponents.qExponents e)
      (fun j => -(v j x).log) := by
  apply represents_of_generator_profiles v W hb hq e x _ hx
  intro j
  simpa only [neg_neg] using (exp_log ((v j).ne_zero_iff.mpr hx0)).symm

end UnconditionalCounterexample.PrimaryWordProfiles
