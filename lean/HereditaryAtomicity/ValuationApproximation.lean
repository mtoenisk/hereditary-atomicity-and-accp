import Mathlib.Analysis.AbsoluteValue.Equivalence
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.RingTheory.Valuation.RankOne

/-!
# Finite exact approximation for real-valued nonarchimedean valuations

Weak approximation of real absolute values gives exact prescribed values for
finitely many distinct nontrivial valuation rings. Each target is an actual
nonzero field element, so no value-surjectivity premise is hidden.
-/

namespace HereditaryAtomicity.ValuationApproximation

open scoped NNReal

universe u v
variable {K : Type u} [Field K]

/-- A nonnegative-real valuation gives a real absolute value. -/
def toRealAbsoluteValue (v : Valuation K ℝ≥0) : AbsoluteValue K ℝ where
  toFun x := v x
  map_mul' x y := by exact_mod_cast v.map_mul x y
  nonneg' x := (v x).coe_nonneg
  eq_zero' x := by simp
  add_le' x y := by
    exact_mod_cast (v.map_add x y).trans
      (max_le_add_of_nonneg (zero_le : (0 : ℝ≥0) ≤ v x) (zero_le : (0 : ℝ≥0) ≤ v y))

@[simp] theorem toRealAbsoluteValue_apply (v : Valuation K ℝ≥0) (x : K) :
    toRealAbsoluteValue v x = (v x : ℝ) := rfl

theorem toRealAbsoluteValue_isNontrivial (v : Valuation K ℝ≥0)
    (hv : v.IsNontrivial) : (toRealAbsoluteValue v).IsNontrivial := by
  obtain ⟨x, hx0, hx1⟩ := hv.exists_val_nontrivial
  refine ⟨x, ?_, ?_⟩
  · exact fun hzero => hx0 (by simp [hzero])
  · simpa using hx1

/-- Equivalent absolute values have the same intrinsic valuation subring. -/
theorem valuationSubring_eq_of_isEquiv {v w : Valuation K ℝ≥0}
    (h : (toRealAbsoluteValue v).IsEquiv (toRealAbsoluteValue w)) :
    v.valuationSubring = w.valuationSubring := by
  ext x
  change v x ≤ 1 ↔ w x ≤ 1
  exact_mod_cast (h.le_one_iff (x := x))

/-- Finite distinct nontrivial valuation rings realize any prescribed finite
list of values already attained by nonzero elements of the field. -/
theorem exists_same_values {ι : Type v} [Finite ι] (v : ι → Valuation K ℝ≥0)
    (hv : ∀ i, (v i).IsNontrivial)
    (hdistinct : Function.Injective fun i => (v i).valuationSubring)
    (a : ι → K) (ha : ∀ i, a i ≠ 0) :
    ∃ x : K, x ≠ 0 ∧ ∀ i, v i x = v i (a i) := by
  classical
  by_cases hι : Nonempty ι
  · let b : ι → AbsoluteValue K ℝ := fun i => toRealAbsoluteValue (v i)
    have hnontrivial : ∀ i, (b i).IsNontrivial :=
      fun i => toRealAbsoluteValue_isNontrivial (v i) (hv i)
    have hnequiv : Pairwise fun i j => ¬ (b i).IsEquiv (b j) := by
      intro i j hij hequiv
      exact hij (hdistinct (valuationSubring_eq_of_isEquiv hequiv))
    let c : ∀ i, WithAbs (b i) := fun i => WithAbs.toAbs (b i) (a i)
    let U : Set (∀ i, WithAbs (b i)) :=
      Set.pi Set.univ fun i => Metric.ball (c i) (b i (a i))
    have hopen : IsOpen U := isOpen_set_pi Set.finite_univ fun _ _ => Metric.isOpen_ball
    have hnonempty : U.Nonempty := by
      refine ⟨c, fun i _ => ?_⟩
      exact Metric.mem_ball_self ((b i).pos_iff.mpr (ha i))
    obtain ⟨x, hx⟩ := (AbsoluteValue.denseRange_algebraMap_pi hnontrivial hnequiv).exists_mem_open
      hopen hnonempty
    have hvalues : ∀ i, v i x = v i (a i) := by
      intro i
      apply (v i).map_eq_of_sub_lt
      have hclose := hx i (Set.mem_univ i)
      change dist (WithAbs.toAbs (b i) x) (WithAbs.toAbs (b i) (a i)) < b i (a i)
        at hclose
      rw [dist_eq_norm, ← WithAbs.toAbs_sub, WithAbs.norm_toAbs_eq] at hclose
      exact_mod_cast hclose
    refine ⟨x, ?_, hvalues⟩
    obtain ⟨i⟩ := hι
    intro hx0
    have hi := hvalues i
    rw [hx0, map_zero] at hi
    exact ((map_ne_zero (v i)).mpr (ha i)) hi.symm
  · have : IsEmpty ι := not_nonempty_iff.mp hι
    exact ⟨1, one_ne_zero, fun i => isEmptyElim i⟩

/-- A rank-one valuation represented in the nonnegative reals through its actual
value group. -/
noncomputable def realValuation {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
    (v : Valuation K Γ₀) [v.RankOne] : Valuation K ℝ≥0 :=
  v.restrict.map (Valuation.RankOne.hom v) (Valuation.RankOne.strictMono v).monotone

/-- The real representative preserves the actual valuation comparison. -/
theorem realValuation_isEquiv {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
    (v : Valuation K Γ₀) [v.RankOne] : (realValuation v).IsEquiv v :=
  (Valuation.isEquiv_map_self_of_strictMono (Valuation.RankOne.hom v)
    (Valuation.RankOne.strictMono v)).trans v.isEquiv_restrict.symm

/-- Finite exact value approximation for arbitrary rank-one codomains. -/
theorem exists_same_values_rankOne {ι : Type v} {Γ : ι → Type*} [Finite ι]
    [∀ i, LinearOrderedCommGroupWithZero (Γ i)]
    (v : ∀ i, Valuation K (Γ i)) [∀ i, (v i).RankOne]
    (hdistinct : Function.Injective fun i => (v i).valuationSubring)
    (a : ι → K) (ha : ∀ i, a i ≠ 0) :
    ∃ x : K, x ≠ 0 ∧ ∀ i, v i x = v i (a i) := by
  have hnontrivial (i : ι) : (realValuation (v i)).IsNontrivial :=
    (realValuation_isEquiv (v i)).isNontrivial_iff.mpr inferInstance
  have hsame (i : ι) : (realValuation (v i)).valuationSubring = (v i).valuationSubring :=
    (Valuation.isEquiv_iff_valuationSubring _ _).mp (realValuation_isEquiv (v i))
  have hinj : Function.Injective fun i => (realValuation (v i)).valuationSubring := by
    intro i j h
    exact hdistinct ((hsame i).symm.trans (h.trans (hsame j)))
  obtain ⟨x, hx, hv⟩ := exists_same_values (fun i => realValuation (v i))
    hnontrivial hinj a ha
  exact ⟨x, hx, fun i => (realValuation_isEquiv (v i)).eq_iff.mp (hv i)⟩

end HereditaryAtomicity.ValuationApproximation
