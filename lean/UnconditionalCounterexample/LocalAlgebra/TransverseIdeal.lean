import UnconditionalCounterexample.LocalAlgebra.ConductorLifting
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.Tactic.Linarith

/-!
# Polynomial subtraction for the transverse ideal

Evaluation at z = p^s t in the subring permits subtraction of the integral polynomial
difference. For each requested precision a single scheduled word suffices, with its
exponent allowed to vary.
-/

namespace UnconditionalCounterexample.LocalAlgebra

open Polynomial

variable {O K : Type*} [CommRing O] [Field K] (T : Subring K)

/-- For an integral-polynomial evaluation into `T`, the evaluated power
congruence gives a quotient in `T` at the same precision. -/
theorem evaluated_power_difference_mem (e : O[X] →+* T) (π : O) (k a : ℕ)
    (P G : O[X]) (hπ : (e (C π) : K) ≠ 0) (hcong : C π ^ k ∣ P - G) :
    (((e P : K) ^ a - (e G : K) ^ a) / (e (C π) : K) ^ k) ∈ T := by
  obtain ⟨Q, hQ⟩ := hcong.trans (sub_dvd_pow_sub_pow P G a)
  have h := congrArg (fun f : O[X] => ((e f : T) : K)) hQ
  simp only [map_sub, map_pow, map_mul, AddSubgroupClass.coe_sub, Subring.coe_pow, Subring.coe_mul] at h
  rw [h, mul_div_cancel_left₀ _ (pow_ne_zero _ hπ)]
  exact (e Q).property

/-- A bounded-exponent word `F^a/H` gives the inverse power needed in the transfer identity.
`V` evaluates to the denominator cleared by `p^b`; `u` is the integral
scalar left after the normalization `P(z) = scale F` and division by `p^k`.
The arithmetic estimates of the successor supply these data. -/
theorem transverse_inverse_power_mem (e : O[X] →+* T) (π : O) (k a r b : ℕ)
    (P G V : O[X]) (F H scale : K) (u : T)
    (hπ : (e (C π) : K) ≠ 0) (hH : H ≠ 0) (har : a ≤ r)
    (hword : F ^ a / H ∈ T) (hV : (e V : K) = (e (C π) : K) ^ b * H)
    (hP : (e P : K) = scale * F) (hu : (u : K) * (e (C π) : K) ^ b * (e (C π) : K) ^ k = scale ^ a)
    (hcong : C π ^ k ∣ P - G) : (e G : K) ^ r / (e (C π) : K) ^ k ∈ T := by
  have hscaled : (e P : K) ^ a / (e (C π) : K) ^ k ∈ T := by
    have heq : (e P : K) ^ a / (e (C π) : K) ^ k = (u : K) * (e V : K) * (F ^ a / H) := by
      rw [hP, mul_pow, ← hu, hV]
      field_simp
    rw [heq]
    exact T.mul_mem (T.mul_mem u.property (e V).property) hword
  have hG := T.sub_mem hscaled (evaluated_power_difference_mem T e π k a P G hπ hcong)
  rw [← sub_div, sub_sub_cancel] at hG
  have h := T.mul_mem hG (T.pow_mem (e G).property (r - a))
  rwa [div_mul_eq_mul_div, ← pow_add, Nat.add_sub_of_le har] at h

/-- The finite schedule only needs `b + k ≤ -v(C₀)` at the chosen stage.
This suffices also for larger powers of the numerator and when `p ∣ a`. -/
theorem exists_integral_transverse_scale (p : ℕ) [Fact p.Prime] (C₀ : ℚ_[p])
    (hC₀ : C₀ ≠ 0) (c b k a : ℕ) (ha : 0 < a)
    (hbudget : (b : ℤ) + k ≤ -C₀.valuation) :
    ∃ u : ℤ_[p], (u : ℚ_[p]) * (p : ℚ_[p]) ^ b * (p : ℚ_[p]) ^ k =
      ((p : ℚ_[p]) ^ c / C₀) ^ a := by
  let q : ℚ_[p] := ((p : ℚ_[p]) ^ c / C₀) ^ a / (p : ℚ_[p]) ^ (b + k)
  have hp : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hq : 0 ≤ q.valuation := by
    dsimp only [q]
    rw [div_eq_mul_inv, Padic.valuation_mul (pow_ne_zero _ (div_ne_zero (pow_ne_zero _ hp) hC₀))
      (inv_ne_zero (pow_ne_zero _ hp)), Padic.valuation_inv, Padic.valuation_pow,
      div_eq_mul_inv, Padic.valuation_mul (pow_ne_zero _ hp) (inv_ne_zero hC₀),
      Padic.valuation_pow, Padic.valuation_inv, Padic.valuation_pow, Padic.valuation_p]
    push_cast
    simp only [mul_one]
    have hnonneg : 0 ≤ (c : ℤ) + -C₀.valuation := by omega
    have hamul := mul_nonneg (show 0 ≤ (a : ℤ) - 1 by omega) hnonneg
    linarith
  refine ⟨⟨q, (Padic.norm_le_one_iff_val_nonneg q).mpr hq⟩, ?_⟩
  change q * _ * _ = _
  rw [mul_assoc, ← pow_add]
  exact div_mul_cancel₀ _ (pow_ne_zero _ hp)

end UnconditionalCounterexample.LocalAlgebra
