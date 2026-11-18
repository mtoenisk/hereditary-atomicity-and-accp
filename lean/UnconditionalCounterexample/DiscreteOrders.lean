import UnconditionalCounterexample.IntersectionStalks
import UnconditionalCounterexample.ValuationProfiles
import Mathlib.Algebra.BigOperators.Finsupp.Basic

namespace UnconditionalCounterexample.DiscreteOrders

open WithZero
open scoped BigOperators

variable {K : Type*} [Field K]

/-- Canonical additive order of an actual discrete multiplicative valuation.
The arbitrary convention at zero is zero; all substantive laws state nonzero
hypotheses where required. -/
def order (v : Valuation K ℤᵐ⁰) (x : K) : ℤ := -log (v x)

@[simp] theorem order_zero (v : Valuation K ℤᵐ⁰) : order v 0 = 0 := by simp [order]
@[simp] theorem order_one (v : Valuation K ℤᵐ⁰) : order v 1 = 0 := by simp [order]

theorem value_eq_exp_neg_order (v : Valuation K ℤᵐ⁰) {x : K} (hx : x ≠ 0) :
    v x = exp (-order v x) := by
  simp only [order, neg_neg]
  exact (exp_log (v.ne_zero_iff.mpr hx)).symm

theorem order_nonneg_iff (v : Valuation K ℤᵐ⁰) {x : K} (hx : x ≠ 0) :
    0 ≤ order v x ↔ v x ≤ 1 := by
  rw [value_eq_exp_neg_order v hx, exp_le_one_iff]
  omega

theorem order_eq_zero_iff (v : Valuation K ℤᵐ⁰) {x : K} (hx : x ≠ 0) :
    order v x = 0 ↔ v x = 1 := by
  rw [value_eq_exp_neg_order v hx, ← exp_zero, exp_inj]
  omega

theorem order_mul (v : Valuation K ℤᵐ⁰) {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) :
    order v (x * y) = order v x + order v y := by
  simp only [order, map_mul, log_mul (v.ne_zero_iff.mpr hx) (v.ne_zero_iff.mpr hy), neg_add]

@[simp] theorem order_inv (v : Valuation K ℤᵐ⁰) (x : K) :
    order v x⁻¹ = -order v x := by simp [order, map_inv₀, log_inv]

theorem order_div (v : Valuation K ℤᵐ⁰) {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) :
    order v (x / y) = order v x - order v y := by
  rw [div_eq_mul_inv, order_mul v hx (inv_ne_zero hy), order_inv, sub_eq_add_neg]

@[simp] theorem order_neg (v : Valuation K ℤᵐ⁰) (x : K) :
    order v (-x) = order v x := by simp [order]

theorem order_zpow (v : Valuation K ℤᵐ⁰) (x : K) (n : ℤ) :
    order v (x ^ n) = n * order v x := by
  simp [order, map_zpow₀, log_zpow]

/-- Natural order used on elements of the actual integral intersection. -/
def natOrder (v : Valuation K ℤᵐ⁰) (x : K) : ℕ := (order v x).toNat

theorem natOrder_cast_of_nonneg (v : Valuation K ℤᵐ⁰) {x : K} (hx : 0 ≤ order v x) :
    (natOrder v x : ℤ) = order v x := Int.toNat_of_nonneg hx

theorem natOrder_cast (v : Valuation K ℤᵐ⁰) {x : K} (hx : x ≠ 0) (hi : v x ≤ 1) :
    (natOrder v x : ℤ) = order v x :=
  natOrder_cast_of_nonneg v ((order_nonneg_iff v hx).mpr hi)

theorem natOrder_mul (v : Valuation K ℤᵐ⁰) {x y : K}
    (hx : x ≠ 0) (hy : y ≠ 0) (hix : v x ≤ 1) (hiy : v y ≤ 1) :
    natOrder v (x * y) = natOrder v x + natOrder v y := by
  have hxord := (order_nonneg_iff v hx).mpr hix
  have hyord := (order_nonneg_iff v hy).mpr hiy
  have hxyord : 0 ≤ order v (x * y) := by rw [order_mul v hx hy]; omega
  apply Int.ofNat_inj.mp
  rw [Int.natCast_add, natOrder_cast_of_nonneg v hxyord,
    natOrder_cast_of_nonneg v hxord, natOrder_cast_of_nonneg v hyord, order_mul v hx hy]

/-- Units of any subring integral for this valuation have order zero. -/
theorem order_eq_zero_of_isUnit (D : Subring K) (v : Valuation K ℤᵐ⁰)
    (hintegral : ∀ x ∈ D, v x ≤ 1) {x : D} (hx : IsUnit x) : order v (x : K) = 0 := by
  obtain ⟨y, hxy⟩ := hx.exists_right_inv
  have hprod : (x : K) * (y : K) = 1 := congrArg Subtype.val hxy
  have hnz : (x : K) * (y : K) ≠ 0 := by rw [hprod]; exact one_ne_zero
  have hx0 := left_ne_zero_of_mul hnz
  have hy0 := right_ne_zero_of_mul hnz
  have hxnonneg := (order_nonneg_iff v hx0).mpr (hintegral x x.property)
  have hynonneg := (order_nonneg_iff v hy0).mpr (hintegral y y.property)
  have hsum := order_mul v hx0 hy0
  rw [hprod, order_one] at hsum
  omega

theorem natOrder_eq_zero_of_isUnit (D : Subring K) (v : Valuation K ℤᵐ⁰)
    (hintegral : ∀ x ∈ D, v x ≤ 1) {x : D} (hx : IsUnit x) : natOrder v (x : K) = 0 := by
  rw [natOrder, order_eq_zero_of_isUnit D v hintegral hx]
  rfl

section FullIntersection

variable {ι : Type*} (v : ι → Valuation K ℤᵐ⁰)

/-- The intersection of all specified discrete valuation rings, including
horizontal rings when they are among the actual supplied places. -/
abbrev fullIntersection : Subring K := IntersectionDomain.intersection ⊤ v

theorem integral (x : fullIntersection v) (i : ι) : v i (x : K) ≤ 1 :=
  ((IntersectionDomain.mem_intersection ⊤ v x).mp x.property).2 i

/-- Vanishing at every actual place characterizes units of the full
intersection. It is crucial that the index family includes every defining
horizontal valuation as well as the vertical valuations. -/
theorem isUnit_iff_order_zero {x : fullIntersection v} (hx : x ≠ 0) :
    IsUnit x ↔ ∀ i, order (v i) (x : K) = 0 := by
  constructor
  · intro hu i
    exact order_eq_zero_of_isUnit (fullIntersection v) (v i)
      (fun z hz => integral v ⟨z, hz⟩ i) hu
  · intro hzero
    have hxK : (x : K) ≠ 0 := fun h => hx (Subtype.ext h)
    have hinv : (x : K)⁻¹ ∈ fullIntersection v := by
      apply (IntersectionDomain.mem_intersection ⊤ v _).mpr
      refine ⟨by trivial, ?_⟩
      intro i
      rw [map_inv₀, (order_eq_zero_iff (v i) hxK).mp (hzero i), inv_one]
    let y : fullIntersection v := ⟨(x : K)⁻¹, hinv⟩
    apply isUnit_iff_exists_inv.mpr
    refine ⟨y, ?_⟩
    apply Subtype.ext
    exact mul_inv_cancel₀ hxK

/-- Divisibility in the actual full intersection is exactly coordinatewise
comparison of additive orders. -/
theorem dvd_iff_order_le {x y : fullIntersection v} (hx : x ≠ 0) (hy : y ≠ 0) :
    x ∣ y ↔ ∀ i, order (v i) (x : K) ≤ order (v i) (y : K) := by
  have hxK : (x : K) ≠ 0 := fun h => hx (Subtype.ext h)
  have hyK : (y : K) ≠ 0 := fun h => hy (Subtype.ext h)
  rw [IntersectionDomain.subring_dvd_iff_div_mem _ x y hx]
  change (y : K) / (x : K) ∈ IntersectionDomain.intersection ⊤ v ↔ _
  rw [IntersectionDomain.mem_intersection]
  simp only [Subring.mem_top, true_and]
  apply forall_congr'
  intro i
  rw [← order_nonneg_iff (v i) (div_ne_zero hyK hxK), order_div (v i) hyK hxK]
  omega

theorem dvd_iff_natOrder_le {x y : fullIntersection v} (hx : x ≠ 0) (hy : y ≠ 0) :
    x ∣ y ↔ ∀ i, natOrder (v i) (x : K) ≤ natOrder (v i) (y : K) := by
  rw [dvd_iff_order_le v hx hy]
  apply forall_congr'
  intro i
  rw [← natOrder_cast (v i) (fun h => hx (Subtype.ext h)) (integral v x i),
    ← natOrder_cast (v i) (fun h => hy (Subtype.ext h)) (integral v y i)]
  exact Int.ofNat_le

end FullIntersection

/-- Natural-valued profiles induced by a complete family of actual discrete
valuations. Only the construction-specific tail, outside-support and principal
congruence facts remain inputs; multiplication, units and divisibility are
proved from the literal full intersection. -/
noncomputable def toValuationProfiles {ι : Type*}
    (v : ProfilePlace ι → Valuation K ℤᵐ⁰)
    (heventually : ∀ x : fullIntersection v, x ≠ 0 → ∃ N : ℕ,
      ∀ j, N ≤ j → order (v (.primary j)) (x : K) = order (v .limit) (x : K))
    (hfinite : ∀ x : fullIntersection v, x ≠ 0 →
      {i | order (v (.outside i)) (x : K) ≠ 0}.Finite)
    (hpure : ∀ x : fullIntersection v, x ≠ 0 → order (v .limit) (x : K) = 0 →
      (∀ i, order (v (.outside i)) (x : K) = 0) →
      TripleCongruent (fun j => order (v (.primary j)) (x : K))) :
    ValuationProfiles (fullIntersection v) ι where
  value p x := natOrder (v p) (x : K)
  value_unit p x hx := natOrder_eq_zero_of_isUnit (fullIntersection v) (v p)
    (fun z hz => integral v ⟨z, hz⟩ p) hx
  value_mul p x y hx hy := natOrder_mul (v p)
    (fun h => hx (Subtype.ext h)) (fun h => hy (Subtype.ext h)) (integral v x p) (integral v y p)
  unit_of_zero x hx hzero := by
    apply (isUnit_iff_order_zero v hx).mpr
    intro p
    rw [← natOrder_cast (v p) (fun h => hx (Subtype.ext h)) (integral v x p), hzero]
    rfl
  eventually_primary x hx := by
    obtain ⟨N, hN⟩ := heventually x hx
    refine ⟨N, ?_⟩
    intro j hj
    apply Int.ofNat_inj.mp
    rw [natOrder_cast (v (.primary j)) (fun h => hx (Subtype.ext h)) (integral v x _),
      natOrder_cast (v .limit) (fun h => hx (Subtype.ext h)) (integral v x _), hN j hj]
  finite_outside x hx := by
    apply (hfinite x hx).subset
    intro i hi hz
    apply hi
    rw [natOrder, hz]
    rfl
  pure_triple x hx hlimit houtside := by
    have hxK : (x : K) ≠ 0 := fun h => hx (Subtype.ext h)
    have hcast (p : ProfilePlace ι) := natOrder_cast (v p) hxK (integral v x p)
    have hl : order (v .limit) (x : K) = 0 := by rw [← hcast .limit, hlimit]; rfl
    have ho : ∀ i, order (v (.outside i)) (x : K) = 0 := by
      intro i
      rw [← hcast (.outside i), houtside]
      rfl
    convert hpure x hx hl ho using 1
    funext j
    exact hcast (.primary j)

/-- The actual coordinatewise divisibility law accompanying the constructed
natural profile object. -/
theorem toValuationProfiles_divisibility {ι : Type*}
    (v : ProfilePlace ι → Valuation K ℤᵐ⁰) (heventually hfinite hpure)
    (x y : fullIntersection v) (hx : x ≠ 0) (hy : y ≠ 0)
    (hle : ∀ p, (toValuationProfiles v heventually hfinite hpure).value p x ≤
      (toValuationProfiles v heventually hfinite hpure).value p y) : x ∣ y :=
  (dvd_iff_natOrder_le v hx hy).mpr hle

end UnconditionalCounterexample.DiscreteOrders
