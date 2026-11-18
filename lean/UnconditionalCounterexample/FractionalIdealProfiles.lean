import UnconditionalCounterexample.DiscreteOrders
import Mathlib.RingTheory.FractionalIdeal.Inverse
import Mathlib.Data.Finset.Max

/-!
# Actual attained profiles of invertible fractional ideals

A coordinate is the minimum additive order attained by an actual ideal element,
expressed as a multiplicative valuation bound plus a witness. Every nonzero
finitely generated fractional ideal has such a minimum. Products add the
coordinates. The resulting homomorphism on actual fractional-ideal units is
injective when the base ring is literally the full valuation intersection.
-/

namespace UnconditionalCounterexample.FractionalIdealProfiles

open WithZero
open scoped nonZeroDivisors

variable {R K : Type*} [CommRing R] [Field K] [Algebra R K]

/-- An actual fractional ideal has value n when its elements all have order
at least n and an element of order exactly n occurs. Zero causes no exception. -/
def HasValue (I : FractionalIdeal R⁰ K) (v : Valuation K ℤᵐ⁰) (n : ℤ) : Prop :=
  (∀ x ∈ I, v x ≤ exp (-n)) ∧ ∃ x ∈ I, v x = exp (-n)

def HasProfile {ι : Type*} (v : ι → Valuation K ℤᵐ⁰)
    (I : FractionalIdeal R⁰ K) (f : ι → ℤ) : Prop := ∀ i, HasValue I (v i) (f i)

theorem HasValue.unique {I : FractionalIdeal R⁰ K} {v : Valuation K ℤᵐ⁰} {a b : ℤ}
    (ha : HasValue I v a) (hb : HasValue I v b) : a = b := by
  obtain ⟨x, hx, hvx⟩ := ha.2
  obtain ⟨y, hy, hvy⟩ := hb.2
  have h1 := hb.1 x hx
  have h2 := ha.1 y hy
  rw [hvx, exp_le_exp] at h1
  rw [hvy, exp_le_exp] at h2
  omega

theorem HasValue.ne_zero {I : FractionalIdeal R⁰ K} {v : Valuation K ℤᵐ⁰} {n : ℤ}
    (h : HasValue I v n) : I ≠ 0 := by
  obtain ⟨x, hx, hv⟩ := h.2
  intro hz
  have hx0 := (FractionalIdeal.mem_zero_iff R⁰).mp (hz ▸ hx)
  rw [hx0, map_zero] at hv
  exact exp_ne_zero hv.symm

/-- The valuation bound is preserved by the actual R-module span. -/
theorem span_bound (v : Valuation K ℤᵐ⁰)
    (hR : ∀ r : R, v (algebraMap R K r) ≤ 1) (s : Set K) (a : ℤᵐ⁰)
    (hs : ∀ x ∈ s, v x ≤ a) :
    ∀ x ∈ Submodule.span R s, v x ≤ a := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem x hx => exact hs x hx
  | zero => simp
  | add x y hx hy ihx ihy => exact (v.map_add x y).trans (max_le ihx ihy)
  | smul r x hx ih =>
    rw [Algebra.smul_def, map_mul]
    exact (mul_le_mul_of_nonneg_right (hR r) zero_le).trans (by simpa using ih)

theorem hasValue_spanSingleton [IsFractionRing R K] (v : Valuation K ℤᵐ⁰)
    (hR : ∀ r : R, v (algebraMap R K r) ≤ 1) (x : K) (hx : x ≠ 0) :
    HasValue (FractionalIdeal.spanSingleton R⁰ x) v (DiscreteOrders.order v x) := by
  have he := DiscreteOrders.value_eq_exp_neg_order v hx
  refine ⟨?_, x, FractionalIdeal.mem_spanSingleton_self R⁰ x, he⟩
  intro y hy
  rw [← he]
  apply span_bound v hR {x} (v x) (by intro z hz; exact le_of_eq (congrArg v (Set.mem_singleton_iff.mp hz))) y
  simpa only [← FractionalIdeal.mem_coe, FractionalIdeal.coe_spanSingleton] using hy

theorem hasValue_one (v : Valuation K ℤᵐ⁰)
    (hR : ∀ r : R, v (algebraMap R K r) ≤ 1) :
    HasValue (1 : FractionalIdeal R⁰ K) v 0 := by
  refine ⟨?_, 1, FractionalIdeal.one_mem_one R⁰, by simp⟩
  intro x hx
  obtain ⟨r, rfl⟩ := (FractionalIdeal.mem_one_iff R⁰).mp hx
  simpa only [neg_zero, exp_zero] using hR r

/-- Product exponents add for the actual fractional-ideal multiplication. -/
theorem HasValue.mul {I J : FractionalIdeal R⁰ K} {v : Valuation K ℤᵐ⁰} {a b : ℤ}
    (hI : HasValue I v a) (hJ : HasValue J v b) : HasValue (I * J) v (a + b) := by
  refine ⟨?_, ?_⟩
  · intro z hz
    refine FractionalIdeal.mul_induction_on hz ?_ ?_
    · intro x hx y hy
      rw [map_mul, neg_add, exp_add]
      exact mul_le_mul' (hI.1 x hx) (hJ.1 y hy)
    · intro x y ihx ihy
      exact (v.map_add x y).trans (max_le ihx ihy)
  · obtain ⟨x, hx, hvx⟩ := hI.2
    obtain ⟨y, hy, hvy⟩ := hJ.2
    refine ⟨x * y, FractionalIdeal.mul_mem_mul hx hy, ?_⟩
    rw [map_mul, hvx, hvy, neg_add, exp_add]

/-- Every nonzero finitely generated fractional ideal has an attained value. -/
theorem exists_value_of_fg (v : Valuation K ℤᵐ⁰)
    (hR : ∀ r : R, v (algebraMap R K r) ≤ 1)
    (I : FractionalIdeal R⁰ K) (hI : (I : Submodule R K).FG) (hI0 : I ≠ 0) :
    ∃ n : ℤ, HasValue I v n := by
  classical
  obtain ⟨s, hs⟩ := hI
  have hs0 : ∃ x ∈ s, x ≠ 0 := by
    by_contra h
    push Not at h
    apply hI0
    apply FractionalIdeal.coeToSubmodule_eq_bot.mp
    rw [← hs]
    apply Submodule.span_eq_bot.mpr
    intro x hx
    exact h x hx
  obtain ⟨x, hx, hx0⟩ := hs0
  obtain ⟨y, hy, hmax⟩ := s.exists_max_image v ⟨x, hx⟩
  have hy0 : y ≠ 0 := by
    intro hz
    have h := hmax x hx
    rw [hz, map_zero] at h
    exact (v.ne_zero_iff.mpr hx0) (le_zero_iff.mp h)
  refine ⟨DiscreteOrders.order v y, ?_, y, ?_, DiscreteOrders.value_eq_exp_neg_order v hy0⟩
  · intro z hz
    rw [← DiscreteOrders.value_eq_exp_neg_order v hy0]
    apply span_bound v hR (s : Set K) (v y) hmax z
    rw [hs]
    exact hz
  · change y ∈ (I : Submodule R K)
    rw [← hs]
    exact Submodule.subset_span hy

/-- Invertible fractional ideals are nonzero and finitely generated, so their
actual profile at every valuation is defined by an attained minimum. -/
theorem exists_value_unit (v : Valuation K ℤᵐ⁰)
    (hR : ∀ r : R, v (algebraMap R K r) ≤ 1) (I : (FractionalIdeal R⁰ K)ˣ) :
    ∃ n : ℤ, HasValue I.val v n :=
  exists_value_of_fg v hR I.val (FractionalIdeal.fg_unit I) (Units.ne_zero I)

noncomputable def value (v : Valuation K ℤᵐ⁰)
    (hR : ∀ r : R, v (algebraMap R K r) ≤ 1) (I : (FractionalIdeal R⁰ K)ˣ) : ℤ :=
  (exists_value_unit v hR I).choose

theorem value_spec (v : Valuation K ℤᵐ⁰)
    (hR : ∀ r : R, v (algebraMap R K r) ≤ 1) (I : (FractionalIdeal R⁰ K)ˣ) :
    HasValue I.val v (value v hR I) := (exists_value_unit v hR I).choose_spec

@[simp] theorem value_one (v : Valuation K ℤᵐ⁰)
    (hR : ∀ r : R, v (algebraMap R K r) ≤ 1) : value v hR 1 = 0 :=
  (value_spec v hR 1).unique (hasValue_one v hR)

theorem value_mul (v : Valuation K ℤᵐ⁰)
    (hR : ∀ r : R, v (algebraMap R K r) ≤ 1) (I J : (FractionalIdeal R⁰ K)ˣ) :
    value v hR (I * J) = value v hR I + value v hR J :=
  (value_spec v hR (I * J)).unique ((value_spec v hR I).mul (value_spec v hR J))

theorem value_inv (v : Valuation K ℤᵐ⁰)
    (hR : ∀ r : R, v (algebraMap R K r) ≤ 1) (I : (FractionalIdeal R⁰ K)ˣ) :
    value v hR I⁻¹ = -value v hR I := by
  have h := value_mul v hR I I⁻¹
  rw [mul_inv_cancel, value_one] at h
  omega

/-- The actual ideal-profile map on the additive form of invertible fractional ideals. -/
noncomputable def profileHom {ι : Type*} (v : ι → Valuation K ℤᵐ⁰)
    (hR : ∀ i r, v i (algebraMap R K r) ≤ 1) :
    Additive (FractionalIdeal R⁰ K)ˣ →+ (ι → ℤ) where
  toFun I i := value (v i) (hR i) I.toMul
  map_zero' := by funext i; exact value_one (v i) (hR i)
  map_add' I J := by funext i; exact value_mul (v i) (hR i) I.toMul J.toMul

theorem profileHom_spec {ι : Type*} (v : ι → Valuation K ℤᵐ⁰)
    (hR : ∀ i r, v i (algebraMap R K r) ≤ 1) (I : Additive (FractionalIdeal R⁰ K)ˣ) :
    HasProfile v I.toMul.val (profileHom v hR I) := fun i => value_spec (v i) (hR i) I.toMul

/-- In the literal full intersection, equal actual profiles determine an
invertible fractional ideal, without a separate ideal-class assumption. -/
theorem profileHom_injective {ι : Type*} (v : ι → Valuation K ℤᵐ⁰)
    (hR : ∀ i r, v i (algebraMap R K r) ≤ 1)
    (hfull : ∀ x : K, x ∈ (1 : FractionalIdeal R⁰ K) ↔ ∀ i, v i x ≤ 1) :
    Function.Injective (profileHom v hR) := by
  have hle (I J : (FractionalIdeal R⁰ K)ˣ)
      (h : ∀ i, value (v i) (hR i) I = value (v i) (hR i) J) : I.val ≤ J.val := by
    have hb : I.val * (J⁻¹).val ≤ (1 : FractionalIdeal R⁰ K) := by
      intro x hx
      apply (hfull x).mpr
      intro i
      have hv := ((value_spec (v i) (hR i) I).mul (value_spec (v i) (hR i) J⁻¹)).1 x hx
      rw [value_inv, h i, add_neg_cancel, neg_zero, exp_zero] at hv
      exact hv
    calc
      I.val = (I.val * (J⁻¹).val) * J.val := by simp only [mul_assoc, Units.inv_mul, mul_one]
      _ ≤ 1 * J.val := by simpa only [mul_comm] using mul_le_mul_right hb J.val
      _ = J.val := one_mul _
  intro I J hij
  change I.toMul = J.toMul
  apply Units.ext
  exact le_antisymm (hle I.toMul J.toMul (congrFun hij))
    (hle J.toMul I.toMul (fun i => (congrFun hij i).symm))

end UnconditionalCounterexample.FractionalIdealProfiles
