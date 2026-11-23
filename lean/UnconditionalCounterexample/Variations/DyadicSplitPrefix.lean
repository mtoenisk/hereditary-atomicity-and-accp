import UnconditionalCounterexample.Variations.DyadicSplitValues
import UnconditionalCounterexample.DiscreteOrders

/-!
# The earlier factor in the dyadic splitting prescription

The prefix already determines the coarse rational function and every
normalized raw except the reserved one. Its coefficient is one. Evaluating
the prefix product therefore gives the factor used in the local targets
before the last polynomial is selected.
-/

noncomputable section
namespace UnconditionalCounterexample.DyadicSplit

open RecursivePrefix DiscreteOrders WithZero
open GuardSupport PrimaryChoices Variations.Univariate MixedStageSelection

/-- Powers of the indicated nonzero field elements, in the unit group of
the field. The exponents may be negative. -/
def weightedProduct {A K : Type*} [CommGroup K] (w : A → K) (e : A →₀ ℤ) : K :=
  e.prod (fun a z => w a ^ z)

/-- Apply the chosen sign, horizontal factors, and scalar prime corrections
in the rational function field before multiplying by normalized raws. -/
def coarseFactor {I A : Type*} (negate : Bool) (horizontal : I → (RatFunc ℚ)ˣ)
    (prime : A → {p : ℕ // p.Prime}) (h : I →₀ ℤ) (a : A →₀ ℤ) : (RatFunc ℚ)ˣ :=
  (if negate then -1 else 1) * weightedProduct horizontal h *
    weightedProduct (fun i => Units.mk0 ((prime i).val : RatFunc ℚ)
      (Nat.cast_ne_zero.mpr (prime i).property.ne_zero)) a

/-- The prospective factor excluding the reserved raw. Its definition uses
only the finite prefix passed to the selector. -/
def prefixFactor {n : ℕ} (P : Prefix n) (base : (RatFunc ℚ)ˣ) (e : ℕ → ℤ) : (RatFunc ℚ)ˣ :=
  base * ∏ j ∈ Finset.range n, (Units.mk0 (P.generators j) (P.generators_ne_zero j)) ^ e j

theorem prefixFactor_eq_chain (C : Chain) (n : ℕ) (base : (RatFunc ℚ)ˣ) (e : ℕ → ℤ) :
    prefixFactor (C.approx n) base e =
      base * ∏ j ∈ Finset.range n, (Units.mk0 (C.generators j) (C.generators_ne_zero j)) ^ e j := by
  unfold prefixFactor
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  congr 1
  exact Units.ext (C.generators_agree n j (Finset.mem_range.mp hj))

/-- Exact value of a split expressed in column labels. A round may permute
its finitely many stages so the reserved label is last. -/
theorem prefixFactor_mul_reserved {A : Type*} [DecidableEq A] (C : Chain) (n : ℕ)
    (base : (RatFunc ℚ)ˣ) (label : ℕ → A) (coeff : A →₀ ℤ) (w : A → (RatFunc ℚ)ˣ)
    (hfrozen : coeff.support ⊆ (Finset.range (n+1)).image label)
    (hdistinct : Set.InjOn label ↑(Finset.range (n+1)))
    (hgen : ∀ j ≤ n, w (label j) = Units.mk0 (C.generators j) (C.generators_ne_zero j))
    (hreserved : coeff (label n) = 1) :
    prefixFactor (C.approx n) base (fun j => coeff (label j)) *
        Units.mk0 (C.generators n) (C.generators_ne_zero n) =
      base * weightedProduct w coeff := by
  rw [weightedProduct, coeff.prod_of_support_subset hfrozen _ (by simp), Finset.prod_image hdistinct]
  have he : (∏ j ∈ Finset.range (n+1), w (label j) ^ coeff (label j)) =
      ∏ j ∈ Finset.range (n+1),
        (Units.mk0 (C.generators j) (C.generators_ne_zero j)) ^ coeff (label j) :=
    Finset.prod_congr rfl (fun j hj => by rw [hgen j (by simpa using hj)])
  rw [he, Finset.prod_range_succ, hreserved, zpow_one, prefixFactor_eq_chain, mul_assoc]

private theorem order_units_prod {K I : Type*} [Field K] (v : Valuation K ℤᵐ⁰)
    (s : Finset I) (f : I → Kˣ) :
    order v ((∏ i ∈ s, f i : Kˣ) : K) = ∑ i ∈ s, order v (f i : K) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi, Units.val_mul,
      order_mul v (f i).ne_zero (Finset.prod s f).ne_zero, ih]

private theorem order_units_mul {K : Type*} [Field K] (v : Valuation K ℤᵐ⁰) (a b : Kˣ) :
    order v ((a*b : Kˣ) : K) = order v (a : K) + order v (b : K) :=
  order_mul v a.ne_zero b.ne_zero

theorem weightedProduct_order {K A : Type*} [Field K] (v : Valuation K ℤᵐ⁰)
    (w : A → Kˣ) (e : A →₀ ℤ) :
    order v ((weightedProduct w e : Kˣ) : K) = e.sum (fun i z => z * order v (w i : K)) := by
  unfold weightedProduct Finsupp.prod Finsupp.sum
  rw [order_units_prod]
  simp only [Units.val_zpow_eq_zpow_val, order_zpow]

/-- The sign contributes zero to every valuation, including at two. -/
theorem coarseFactor_order {I A : Type*} (v : Valuation (RatFunc ℚ) ℤᵐ⁰) (negate : Bool)
    (horizontal : I → (RatFunc ℚ)ˣ) (prime : A → {p : ℕ // p.Prime})
    (h : I →₀ ℤ) (a : A →₀ ℤ) :
    order v (coarseFactor negate horizontal prime h a : RatFunc ℚ) =
      h.sum (fun i z => z * order v (horizontal i : RatFunc ℚ)) +
      a.sum (fun i z => z * order v ((prime i).val : RatFunc ℚ)) := by
  let sign : (RatFunc ℚ)ˣ := if negate then -1 else 1
  have hsign : order v (sign : RatFunc ℚ) = 0 := by cases negate <;> simp [sign]
  unfold coarseFactor
  rw [order_units_mul, order_units_mul, hsign, zero_add, weightedProduct_order, weightedProduct_order]
  rfl

/-- At a processed prime the order of the earlier factor is computed using
the orders of polynomials already selected and the fixed coarse data. -/
theorem prefixFactor_order {n : ℕ} (P : Prefix n) (base : (RatFunc ℚ)ˣ) (e : ℕ → ℤ)
    (v : Valuation (RatFunc ℚ) ℤᵐ⁰) :
    order v (prefixFactor P base e : RatFunc ℚ) = order v (base : RatFunc ℚ) +
      ∑ j ∈ Finset.range n, e j * order v (P.generators j) := by
  unfold prefixFactor
  rw [order_units_mul, order_units_prod]
  simp only [Units.val_zpow_eq_zpow_val, Units.val_mk0, order_zpow]

/-- A branch-order calculation involving only the prefix supplies the norm
match required by the reserved-target callback. Inactive branches receive
the constant one. -/
theorem prefixFactor_branch_norm {n : ℕ} (P : Prefix n) (base : (RatFunc ℚ)ˣ) (e : ℕ → ℤ)
    {p : PrimeIndex} (site : Site p) (b first : Bool) (x : (RatFunc ℚ)ˣ)
    (h : ∀ hb : Active site.paired b,
      let v := EvaluationDVR.valuation p.val (site.evaluate b hb)
      order v (base : RatFunc ℚ) + ∑ j ∈ Finset.range n, e j * order v (P.generators j) =
        if first then order v (x : RatFunc ℚ) else 0) :
    ‖branchValue site b (prefixFactor P base e : RatFunc ℚ)‖ =
      if first then ‖branchValue site b (x : RatFunc ℚ)‖ else 1 := by
  classical
  by_cases hb : Active site.paired b
  · let φ := site.evaluate b hb
    let v := EvaluationDVR.valuation p.val φ
    have hv (y : (RatFunc ℚ)ˣ) : order v (y : RatFunc ℚ) = (φ (y : RatFunc ℚ)).valuation := by
      have hy : φ (y : RatFunc ℚ) ≠ 0 := (map_ne_zero φ).mpr y.ne_zero
      change -log (Padic.mulValuation (φ (y : RatFunc ℚ))) = _
      simp only [Padic.mulValuation_toFun, hy, ite_false, log_exp, neg_neg]
    have he := h hb
    dsimp only at he
    rw [← prefixFactor_order] at he
    simp only [branchValue, dite_eq_left hb]
    change ‖φ (prefixFactor P base e : RatFunc ℚ)‖ = if first then ‖φ (x : RatFunc ℚ)‖ else 1
    rw [Padic.norm_eq_zpow_neg_valuation ((map_ne_zero φ).mpr (prefixFactor P base e).ne_zero),
      ← hv, he]
    cases first
    · simp
    · simp only [ite_true]
      rw [hv, Padic.norm_eq_zpow_neg_valuation ((map_ne_zero φ).mpr x.ne_zero)]
  · cases first <;> simp [branchValue, hb]

end UnconditionalCounterexample.DyadicSplit
