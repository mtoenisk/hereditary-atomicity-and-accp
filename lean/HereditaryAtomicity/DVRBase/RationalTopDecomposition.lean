import HereditaryAtomicity.DVRBase.RationalCoefficientBase
import HereditaryAtomicity.DVRBase.SourceDomination

/-!
# Actual rational-prime decompositions of integer tops

Integer tops are decomposed inside the literal rational-prime coefficient
DVR. Powering retains the prescribed divisibility of the new exponent, and
coefficient units supply the exact normalization of the top.
-/

noncomputable section
namespace HereditaryAtomicity.DVRBase
open scoped NNReal
variable {K : Type*} [Field K] [CharZero K]

/-- Algebraicity over the rational field gives algebraicity over the integers
for every actual unital source subring. -/
theorem subring_isAlgebraic_int_of_rat [Algebra.IsAlgebraic ℚ K]
    (D : Subring K) : Algebra.IsAlgebraic ℤ D := by
  let : Algebra.IsAlgebraic ℤ K := ⟨fun x =>
    (IsFractionRing.isAlgebraic_iff ℤ ℚ K).mpr (Algebra.IsAlgebraic.isAlgebraic x)⟩
  exact Algebra.IsAlgebraic.tower_bot_of_injective (A := K) Subtype.val_injective

/-- A nonzero integer has an actual unit-times-prime-power decomposition in
canonical ℤ_(p), with no prescribed-order assumption. -/
theorem rational_integer_eq_unit_mul_prime_pow
    (p : ℕ) [Fact p.Prime] (m : ℤ) (hm : m ≠ 0) :
    ∃ (e : ℕ) (u : (rationalCoefficientRing p K)ˣ),
      (m : K) = ((u : rationalCoefficientRing p K) : K) * (p : K) ^ e := by
  have hmO : (m : rationalCoefficientRing p K) ≠ 0 := by
    intro hz
    have hK : (m : K) = 0 := congrArg Subtype.val hz
    exact hm (Int.cast_eq_zero.mp hK)
  obtain ⟨e, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hmO
    (rationalCoefficientUniformizer_irreducible p K)
  refine ⟨e, u, ?_⟩
  have huK := congrArg (rationalCoefficientRing p K).subtype hu
  change (m : K) = ((u : rationalCoefficientRing p K) : K) *
    (rationalCoefficientUniformizer p K : K) ^ e at huK
  rwa [rationalCoefficientUniformizer_coe] at huK

/-- Divisibility of the integer by p forces positive exponent in every actual
unit decomposition in ℤ_(p). -/
theorem rational_integer_decomposition_pos
    (p : ℕ) [Fact p.Prime] (m : ℤ) (hm : (p : ℤ) ∣ m)
    (e : ℕ) (u : (rationalCoefficientRing p K)ˣ)
    (hu : (m : K) = ((u : rationalCoefficientRing p K) : K) * (p : K) ^ e) : 0 < e := by
  have hpdiv : rationalCoefficientUniformizer p K ∣ (m : rationalCoefficientRing p K) := by
    obtain ⟨z, hz⟩ := hm
    refine ⟨(z : rationalCoefficientRing p K), ?_⟩
    apply Subtype.ext
    change (m : K) = (rationalCoefficientUniformizer p K : K) * (z : K)
    rw [rationalCoefficientUniformizer_coe, hz, Int.cast_mul, Int.cast_natCast]
  apply Nat.pos_of_ne_zero
  intro he
  have hmU : (m : rationalCoefficientRing p K) = u := by
    apply Subtype.ext
    change (m : K) = ((u : rationalCoefficientRing p K) : K)
    simpa only [he, pow_zero, mul_one] using hu
  exact (rationalCoefficientUniformizer_irreducible p K).not_isUnit
    (isUnit_of_dvd_unit hpdiv (hmU ▸ u.isUnit))

/-- Positive integer decomposition when the chosen rational prime divides it. -/
theorem rational_integer_eq_unit_mul_prime_pow_pos
    (p : ℕ) [Fact p.Prime] (m : ℤ) (hm : m ≠ 0) (hpm : (p : ℤ) ∣ m) :
    ∃ (e : ℕ) (u : (rationalCoefficientRing p K)ˣ), 0 < e ∧
      (m : K) = ((u : rationalCoefficientRing p K) : K) * (p : K) ^ e := by
  obtain ⟨e, u, hu⟩ := rational_integer_eq_unit_mul_prime_pow (K := K) p m hm
  exact ⟨e, u, rational_integer_decomposition_pos p m hpm e u hu, hu⟩

/-- An integer in the maximal ideal of a local ring of residue prime p is
actually divisible by p in ℤ. -/
theorem int_dvd_of_mem_local_maximal
    (p : ℕ) [Fact p.Prime] (A : Type*) [CommRing A] [IsLocalRing A]
    (hpA : (p : A) ∈ IsLocalRing.maximalIdeal A)
    (m : ℤ) (hmA : (m : A) ∈ IsLocalRing.maximalIdeal A) : (p : ℤ) ∣ m := by
  apply Ideal.mem_span_singleton.mp
  change m ∈ rationalPrimeIdeal p
  rw [← intResiduePrime_eq_rationalPrimeIdeal p A hpA]
  change IsLocalRing.residue A (m : A) = 0
  exact (IsLocalRing.residue_eq_zero_iff _).mpr hmA

/-- Taking a positive h-th power gives a positive top exponent divisible by h,
with its actual coefficient unit retained. -/
theorem rational_integer_pow_eq_unit_mul_prime_pow
    (p : ℕ) [Fact p.Prime] (m : ℤ) (hm : m ≠ 0) (hpm : (p : ℤ) ∣ m)
    (h : ℕ) (hh : 0 < h) :
    ∃ (e κ : ℕ) (u : (rationalCoefficientRing p K)ˣ),
      0 < e ∧ κ = h * e ∧ 0 < κ ∧ h ∣ κ ∧
      (m : K) ^ h = ((u : rationalCoefficientRing p K) : K) * (p : K) ^ κ := by
  obtain ⟨e, u, he, hu⟩ := rational_integer_eq_unit_mul_prime_pow_pos (K := K) p m hm hpm
  refine ⟨e, h * e, u ^ h, he, rfl, Nat.mul_pos hh he, dvd_mul_right h e, ?_⟩
  change (m : K) ^ h = ((u : rationalCoefficientRing p K) : K) ^ h * (p : K) ^ (h * e)
  rw [hu, mul_pow, ← pow_mul, Nat.mul_comm e h]

/-- The inverse coefficient unit gives an exact prime-power top after
normalization. -/
theorem rational_integer_pow_normalized_top
    (p : ℕ) [Fact p.Prime] (m : ℤ) (h κ : ℕ)
    (u : (rationalCoefficientRing p K)ˣ)
    (hu : (m : K) ^ h = ((u : rationalCoefficientRing p K) : K) * (p : K) ^ κ) :
    (((u⁻¹ : (rationalCoefficientRing p K)ˣ) : rationalCoefficientRing p K) : K) *
      (m : K) ^ h = (p : K) ^ κ := by
  rw [hu, ← mul_assoc]
  have hinv : (((u⁻¹ : (rationalCoefficientRing p K)ˣ) : rationalCoefficientRing p K) : K) *
      ((u : rationalCoefficientRing p K) : K) = 1 := by
    exact congrArg (rationalCoefficientRing p K).subtype u.inv_val
  rw [hinv, one_mul]

/-- Actual divisibility by p^h in a valuation-bounded source ring supplies
the normalized endpoint order bound. -/
theorem rational_order_ge_of_prime_pow_dvd
    (p : ℕ) [Fact p.Prime] (R : Subring K)
    (w : Valuation K ℝ≥0) (hR : ∀ a : R, w (a : K) ≤ 1)
    (hnorm : realValuationOrder w (p : K) = 1)
    (h : ℕ) (b : R) (hb : b ≠ 0) (hdiv : (p : R) ^ h ∣ b) :
    (h : ℝ) ≤ realValuationOrder w (b : K) := by
  obtain ⟨c, hc⟩ := hdiv
  have hc0 : c ≠ 0 := by intro hz; exact hb (by rw [hc, hz, mul_zero])
  have hp0 : (p : K) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have heq := congrArg R.subtype hc
  change (b : K) = (p : K) ^ h * (c : K) at heq
  rw [heq, realValuationOrder_mul w (pow_ne_zero _ hp0) (Subtype.coe_ne_coe.mpr hc0),
    realValuationOrder_pow, hnorm, mul_one]
  exact le_add_of_nonneg_right
    ((realValuationOrder_nonneg_iff w (Subtype.coe_ne_coe.mpr hc0)).mpr (hR c))

/-- The original source slack s^h dividing b yields order at least one after
normalizing by an actual coefficient unit. Only boundedness and p|s are used. -/
theorem rational_normalized_endpoint_order_ge_one
    (p : ℕ) [Fact p.Prime] (R : Subring K)
    (w : Valuation K ℝ≥0) (hR : ∀ a : R, w (a : K) ≤ 1)
    (hO : ∀ a : rationalCoefficientRing p K, w (a : K) ≤ 1)
    (hnorm : realValuationOrder w (p : K) = 1)
    (h : ℕ) (hh : 0 < h) (s b x : R) (hb : b ≠ 0) (hx : x ≠ 0)
    (hps : (p : R) ∣ s) (hsb : s ^ h ∣ b)
    (u : (rationalCoefficientRing p K)ˣ) :
    1 ≤ realValuationOrder w
      ((((u⁻¹ : (rationalCoefficientRing p K)ˣ) : rationalCoefficientRing p K) : K) *
        (b : K) * (x : K)) := by
  have hbnd := rational_order_ge_of_prime_pow_dvd p R w hR hnorm h b hb
    ((pow_dvd_pow_of_dvd hps h).trans hsb)
  have hxnd := (realValuationOrder_nonneg_iff w (Subtype.coe_ne_coe.mpr hx)).mpr (hR x)
  have hu0 : ((((u⁻¹ : (rationalCoefficientRing p K)ˣ) : rationalCoefficientRing p K) : K)) ≠ 0 :=
    Subtype.coe_ne_coe.mpr (u⁻¹).ne_zero
  rw [realValuationOrder_mul w (mul_ne_zero hu0 (Subtype.coe_ne_coe.mpr hb))
      (Subtype.coe_ne_coe.mpr hx),
    realValuationOrder_mul w hu0 (Subtype.coe_ne_coe.mpr hb),
    coefficient_unit_order (rationalCoefficientRing p K) w hO (u⁻¹), zero_add]
  have hhR : (1 : ℝ) ≤ h := by exact_mod_cast hh
  linarith

end HereditaryAtomicity.DVRBase
