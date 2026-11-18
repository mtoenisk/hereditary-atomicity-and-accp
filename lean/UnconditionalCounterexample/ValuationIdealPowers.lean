import UnconditionalCounterexample.DiscreteOrders
import Mathlib.RingTheory.Valuation.Discrete.Basic
import Mathlib.RingTheory.LocalRing.RingHom.Basic

/-!
# Exact normalized principal powers in a discrete valuation ring

An element of value exp(-1) generates the actual maximal ideal, and an integral
nonzero element generates its natOrder-th power. Ring equivalences transport
this equality to the corresponding actual localizations.
-/

noncomputable section
namespace UnconditionalCounterexample.ValuationIdealPowers
open WithZero DiscreteOrders
variable {K : Type*} [Field K]

lemma mem_span_iff_value_le (v : Valuation K ℤᵐ⁰) (x y : v.valuationSubring) :
    y ∈ Ideal.span ({x} : Set v.valuationSubring) ↔ v (y : K) ≤ v (x : K) := by
  change y ∈ (Ideal.span ({x} : Set v.integer) : Set v.integer) ↔ _
  rw [Valuation.integer.coe_span_singleton_eq_setOfPred_le_v_coe]
  rfl

/-- A value-one element generates the actual maximal ideal, without an
additional choice of DVR uniformizer or a valuation rescaling. -/
theorem maximalIdeal_eq_span (v : Valuation K ℤᵐ⁰) (π : v.valuationSubring)
    (hπ : v (π : K) = exp (-1 : ℤ)) :
    IsLocalRing.maximalIdeal v.valuationSubring = Ideal.span ({π} : Set v.valuationSubring) := by
  ext x
  rw [Valuation.mem_maximalIdeal_iff, mem_span_iff_value_le, hπ]
  by_cases hx : (x : K) = 0
  · simp [hx]
  · rw [value_eq_exp_neg_order v hx, ← exp_zero, exp_lt_exp, exp_le_exp]
    omega

/-- Exact principal ideal power measured by the actual normalized order. -/
theorem span_eq_maximalIdeal_pow (v : Valuation K ℤᵐ⁰) (π : v.valuationSubring)
    (hπ : v (π : K) = exp (-1 : ℤ)) (x : v.valuationSubring) (hx : x ≠ 0) :
    Ideal.span ({x} : Set v.valuationSubring) =
      IsLocalRing.maximalIdeal v.valuationSubring ^ natOrder v (x : K) := by
  rw [maximalIdeal_eq_span v π hπ, Ideal.span_singleton_pow]
  ext y
  rw [mem_span_iff_value_le, mem_span_iff_value_le]
  have hxK : (x : K) ≠ 0 := fun h => hx (Subtype.ext h)
  have hcast := natOrder_cast v hxK x.property
  have hpow : v ((π ^ natOrder v (x : K) : v.valuationSubring) : K) = v (x : K) := by
    change v ((π : K) ^ natOrder v (x : K)) = _
    rw [map_pow, hπ, ← exp_nsmul, value_eq_exp_neg_order v hxK]
    congr 1
    simpa only [nsmul_eq_mul, mul_neg, mul_one] using congrArg Neg.neg hcast
  rw [hpow]

/-- Transport the exact principal power across an actual local-ring equivalence. -/
theorem span_eq_maximalIdeal_pow_of_equiv {R : Type*} [CommRing R] [IsLocalRing R]
    (v : Valuation K ℤᵐ⁰) (π : v.valuationSubring) (hπ : v (π : K) = exp (-1 : ℤ))
    (e : R ≃+* v.valuationSubring) (x : R) (hx : x ≠ 0) :
    Ideal.span ({x} : Set R) = IsLocalRing.maximalIdeal R ^ natOrder v (e x : K) := by
  apply (Ideal.relIsoOfBijective e.toRingHom e.bijective).symm.injective
  change (Ideal.span ({x} : Set R)).map e.toRingHom =
    (IsLocalRing.maximalIdeal R ^ natOrder v (e x : K)).map e.toRingHom
  have hm : (IsLocalRing.maximalIdeal R).map e.toRingHom =
      IsLocalRing.maximalIdeal v.valuationSubring := IsLocalRing.map_ringEquiv_maximalIdeal e
  rw [Ideal.map_span, Set.image_singleton, Ideal.map_pow, hm]
  exact span_eq_maximalIdeal_pow v π hπ (e x) (fun h => hx (e.injective (h.trans (e.map_zero).symm)))

end UnconditionalCounterexample.ValuationIdealPowers
