import UnconditionalCounterexample.PrincipalProfiles
import UnconditionalCounterexample.PrimaryStabilization
import Mathlib.RingTheory.DedekindDomain.AdicValuation

/-!
# Actual horizontal valuations and the pole algebra

Monic irreducible polynomials define the usual normalized height-one valuations
on the rational function field. Their additive orders are exactly the canonical
signed numerator-minus-denominator exponents from `PrincipalProfiles`.

For any nonzero polynomial denominator set S, the pole algebra is the
intersection of the valuation rings at irreducibles dividing none of S.
Vanishing at these retained places detects pole-algebra units, and equal
retained coordinates make the quotient a unit. Every nonzero rational function
has finite horizontal support. The X-coordinate agrees with the order at zero
used in `PrimaryStabilization`; it is retained when selected denominators have
nonzero constant coefficients. No claim about the infinite place is made.
-/

namespace UnconditionalCounterexample.HorizontalOrders

open Polynomial PrincipalProfiles
open scoped WithZero

noncomputable section

variable {k : Type*} [Field k]

/-- A horizontal prime is retained exactly when it divides no inverted polynomial. -/
def Retained (S : Set k[X]) (p : MonicIrreducible k) : Prop :=
  ∀ q ∈ S, ¬ p.val ∣ q

theorem multiplicities_nonneg {α : Type*} (s : Multiset α) (a : α) :
    0 ≤ multiplicities s a := by
  classical
  simp [multiplicities]

theorem exponent_nonneg_of_mem (S : Set k[X]) (hS : ∀ q ∈ S, q ≠ 0)
    (x : RatFunc k) (hx : x ≠ 0) (hmem : x ∈ PoleAlgebra.generated S)
    (p : MonicIrreducible k) (hp : Retained S p) : 0 ≤ exponents x hx p := by
  have hnot : p ∉ factors x.denom x.denom_ne_zero := by
    intro h
    obtain ⟨q, hq, hpq⟩ := PoleAlgebra.denom_prime_support S hS hmem
      p.property.2.prime ((mem_factors_iff _ _ p).mp h)
    exact hp q hq hpq
  have hzero : multiplicities (factors x.denom x.denom_ne_zero) p = 0 := by
    simpa only [← mem_multiplicities_support, Finsupp.notMem_support_iff] using hnot
  simpa only [exponents, Finsupp.sub_apply, hzero, sub_zero] using
    multiplicities_nonneg (factors x.num (RatFunc.num_ne_zero hx)) p

theorem factor_zpow_mem (S : Set k[X]) (hS : ∀ q ∈ S, q ≠ 0)
    (p : MonicIrreducible k) (z : ℤ)
    (h : 0 ≤ z ∨ ∃ q ∈ S, p.val ∣ q) :
    factor p ^ z ∈ PoleAlgebra.generated S := by
  cases z with
  | ofNat n =>
    simpa only [Int.ofNat_eq_natCast, zpow_natCast, PrincipalProfiles.factor] using
      (PoleAlgebra.generated S).pow_mem (PoleAlgebra.polynomial_mem S p.val) n
  | negSucc n =>
    obtain ⟨q, hq, hpq⟩ := h.resolve_left (by omega)
    have hinv := PoleAlgebra.inverse_factor_mem (Submonoid.subset_closure hq) (hS q hq) hpq
    simpa only [zpow_negSucc, inv_pow, PrincipalProfiles.factor] using
      (PoleAlgebra.generated S).pow_mem hinv (n + 1)

theorem word_mem_of_retained_nonneg (S : Set k[X]) (hS : ∀ q ∈ S, q ≠ 0)
    (e : MonicIrreducible k →₀ ℤ) (h : ∀ p, Retained S p → 0 ≤ e p) :
    word PrincipalProfiles.factor e ∈ PoleAlgebra.generated S := by
  classical
  apply Submonoid.prod_mem
  intro p _
  apply factor_zpow_mem S hS p (e p)
  by_cases hsel : ∃ q ∈ S, p.val ∣ q
  · exact Or.inr hsel
  · exact Or.inl (h p (fun q hq hpq => hsel ⟨q, hq, hpq⟩))

theorem mem_iff_retained_exponents_nonneg (S : Set k[X]) (hS : ∀ q ∈ S, q ≠ 0)
    (x : RatFunc k) (hx : x ≠ 0) :
    x ∈ PoleAlgebra.generated S ↔ ∀ p, Retained S p → 0 ≤ exponents x hx p := by
  constructor
  · exact exponent_nonneg_of_mem S hS x hx
  · intro h
    rw [signed_factorization x hx]
    exact (PoleAlgebra.generated S).mul_mem
      ((PoleAlgebra.generated S).algebraMap_mem _) (word_mem_of_retained_nonneg S hS _ h)

/-- Vanishing retained coordinates detects actual units of the pole algebra. -/
theorem mem_and_inv_mem_iff_retained_exponents_eq_zero
    (S : Set k[X]) (hS : ∀ q ∈ S, q ≠ 0) (x : RatFunc k) (hx : x ≠ 0) :
    (x ∈ PoleAlgebra.generated S ∧ x⁻¹ ∈ PoleAlgebra.generated S) ↔
      ∀ p, Retained S p → exponents x hx p = 0 := by
  classical
  constructor
  · rintro ⟨hmem, hinv⟩ p hp
    by_contra he
    obtain ⟨q, hq, hdvd⟩ := exponent_support_of_unit S hS x hx hmem hinv p
      (Finsupp.mem_support_iff.mpr he)
    exact hp q hq hdvd
  · intro h
    refine ⟨(mem_iff_retained_exponents_nonneg S hS x hx).mpr
      (fun p hp => le_of_eq (h p hp).symm), ?_⟩
    rw [signed_factorization x hx, mul_inv_rev, ← word_neg, ← map_inv₀]
    exact (PoleAlgebra.generated S).mul_mem
      (word_mem_of_retained_nonneg S hS _ (by
        intro p hp
        simp only [Finsupp.neg_apply, h p hp, neg_zero, le_refl]))
      ((PoleAlgebra.generated S).algebraMap_mem _)

/-- Equality of retained coordinates makes the quotient an actual pole-algebra unit. -/
theorem div_mem_and_inv_mem_of_retained_exponents_eq
    (S : Set k[X]) (hS : ∀ q ∈ S, q ≠ 0)
    (x y : RatFunc k) (hx : x ≠ 0) (hy : y ≠ 0)
    (h : ∀ p, Retained S p → exponents x hx p = exponents y hy p) :
    x / y ∈ PoleAlgebra.generated S ∧ (x / y)⁻¹ ∈ PoleAlgebra.generated S := by
  have he (p : MonicIrreducible k) (hp : Retained S p) :
      (exponents x hx - exponents y hy) p = 0 := by
    simp only [Finsupp.sub_apply, h p hp, sub_self]
  have hrep : x / y =
      RatFunc.C ((x.num.leadingCoeff / x.denom.leadingCoeff) /
        (y.num.leadingCoeff / y.denom.leadingCoeff)) *
      word PrincipalProfiles.factor (exponents x hx - exponents y hy) := by
    conv_lhs => rw [signed_factorization x hx, signed_factorization y hy]
    rw [word_sub _ factor_ne_zero]
    simp only [map_div₀]
    ring
  rw [hrep]
  constructor
  · exact (PoleAlgebra.generated S).mul_mem ((PoleAlgebra.generated S).algebraMap_mem _)
      (word_mem_of_retained_nonneg S hS _ (fun p hp => le_of_eq (he p hp).symm))
  · rw [mul_inv_rev, ← word_neg, ← map_inv₀]
    exact (PoleAlgebra.generated S).mul_mem
      (word_mem_of_retained_nonneg S hS _ (by
        intro p hp
        simp only [Finsupp.neg_apply, he p hp, neg_zero, le_refl]))
      ((PoleAlgebra.generated S).algebraMap_mem _)

/-- The actual height-one point associated with a monic irreducible. -/
def point (p : MonicIrreducible k) : IsDedekindDomain.HeightOneSpectrum k[X] where
  asIdeal := Ideal.span {p.val}
  isPrime := (Ideal.span_singleton_prime p.property.1.ne_zero).mpr p.property.2.prime
  ne_bot := by
    intro h
    exact p.property.1.ne_zero (Ideal.span_singleton_eq_bot.mp h)

/-- The usual normalized discrete valuation on k(t) at p. -/
def valuation (p : MonicIrreducible k) : Valuation (RatFunc k) ℤᵐ⁰ :=
  (point p).valuation (RatFunc k)

@[simp] theorem valuation_factor_self (p : MonicIrreducible k) :
    valuation p (PrincipalProfiles.factor p) = WithZero.exp (-1 : ℤ) := by
  rw [valuation, PrincipalProfiles.factor,
    IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
  exact (point p).intValuation_singleton p.property.1.ne_zero rfl

@[simp] theorem valuation_factor_of_ne (p q : MonicIrreducible k) (h : q ≠ p) :
    valuation p (PrincipalProfiles.factor q) = 1 := by
  rw [valuation, PrincipalProfiles.factor,
    IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
  apply IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff.mpr
  intro hmem
  have hdvd : p.val ∣ q.val := Ideal.mem_span_singleton.mp hmem
  have heq := Polynomial.eq_of_monic_of_associated p.property.1 q.property.1
    (p.property.2.associated_of_dvd q.property.2 hdvd)
  exact h (Subtype.ext heq.symm)

@[simp] theorem valuation_constant (p : MonicIrreducible k) (c : k) (hc : c ≠ 0) :
    valuation p (RatFunc.C c) = 1 := by
  rw [← RatFunc.algebraMap_C, valuation,
    IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
  apply IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff.mpr
  exact Ideal.notMem_of_isUnit _ (Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr hc))

theorem valuation_word (p : MonicIrreducible k) (e : MonicIrreducible k →₀ ℤ) :
    valuation p (word PrincipalProfiles.factor e) = WithZero.exp (-(e p)) := by
  classical
  simp only [word, Finsupp.prod, map_prod, map_zpow₀]
  rw [Finset.prod_eq_single p]
  · rw [valuation_factor_self, ← WithZero.exp_zsmul]
    congr 1
    simp
  · intro q _ hqp
    rw [valuation_factor_of_ne p q hqp, one_zpow]
  · intro hp
    have he : e p = 0 := Finsupp.notMem_support_iff.mp hp
    rw [he, zpow_zero]

/-- Canonical signed exponents are the actual normalized discrete orders. -/
theorem valuation_eq_exp_neg_exponents (p : MonicIrreducible k)
    (x : RatFunc k) (hx : x ≠ 0) :
    valuation p x = WithZero.exp (-(exponents x hx p)) := by
  conv_lhs => rw [signed_factorization x hx]
  rw [map_mul, valuation_constant p _ (div_ne_zero
    (Polynomial.leadingCoeff_ne_zero.mpr (RatFunc.num_ne_zero hx))
    (Polynomial.leadingCoeff_ne_zero.mpr x.denom_ne_zero)), one_mul, valuation_word]

theorem retained_range_iff {ι : Type*} (F : ι → k[X])
    (hF : ∀ i, (F i).Monic ∧ Irreducible (F i)) (p : MonicIrreducible k) :
    Retained (Set.range F) p ↔ p.val ∉ Set.range F := by
  constructor
  · rintro h ⟨i, hi⟩
    exact h (F i) (Set.mem_range_self i) (hi ▸ dvd_rfl)
  · intro h q hq hpq
    obtain ⟨i, rfl⟩ := hq
    have heq := Polynomial.eq_of_monic_of_associated p.property.1 (hF i).1
      (p.property.2.associated_of_dvd (hF i).2 hpq)
    exact h ⟨i, heq.symm⟩

theorem mem_iff_retained_valuations_le_one (S : Set k[X]) (hS : ∀ q ∈ S, q ≠ 0)
    (x : RatFunc k) (hx : x ≠ 0) :
    x ∈ PoleAlgebra.generated S ↔ ∀ p, Retained S p → valuation p x ≤ 1 := by
  rw [mem_iff_retained_exponents_nonneg S hS x hx]
  simp only [valuation_eq_exp_neg_exponents _ x hx, ← WithZero.exp_zero,
    WithZero.exp_le_exp, neg_nonpos]

theorem mem_and_inv_mem_iff_retained_valuations_eq_one
    (S : Set k[X]) (hS : ∀ q ∈ S, q ≠ 0) (x : RatFunc k) (hx : x ≠ 0) :
    (x ∈ PoleAlgebra.generated S ∧ x⁻¹ ∈ PoleAlgebra.generated S) ↔
      ∀ p, Retained S p → valuation p x = 1 := by
  rw [mem_and_inv_mem_iff_retained_exponents_eq_zero S hS x hx]
  simp only [valuation_eq_exp_neg_exponents _ x hx, ← WithZero.exp_zero,
    WithZero.exp_inj, neg_eq_zero]

theorem div_mem_and_inv_mem_of_retained_valuations_eq
    (S : Set k[X]) (hS : ∀ q ∈ S, q ≠ 0)
    (x y : RatFunc k) (hx : x ≠ 0) (hy : y ≠ 0)
    (h : ∀ p, Retained S p → valuation p x = valuation p y) :
    x / y ∈ PoleAlgebra.generated S ∧ (x / y)⁻¹ ∈ PoleAlgebra.generated S := by
  apply div_mem_and_inv_mem_of_retained_exponents_eq S hS x y hx hy
  intro p hp
  have he := h p hp
  rw [valuation_eq_exp_neg_exponents p x hx,
    valuation_eq_exp_neg_exponents p y hy, WithZero.exp_inj] at he
  exact neg_injective he

theorem neg_log_valuation_eq_exponents (p : MonicIrreducible k)
    (x : RatFunc k) (hx : x ≠ 0) :
    -WithZero.log (valuation p x) = exponents x hx p := by
  rw [valuation_eq_exp_neg_exponents p x hx, WithZero.log_exp, neg_neg]

theorem finite_valuation_support (x : RatFunc k) (hx : x ≠ 0) :
    Set.Finite {p : MonicIrreducible k | valuation p x ≠ 1} := by
  classical
  apply (exponents x hx).support.finite_toSet.subset
  intro p hp
  apply Finsupp.mem_support_iff.mpr
  intro he
  apply hp
  rw [valuation_eq_exp_neg_exponents p x hx, he, neg_zero, WithZero.exp_zero]

theorem exponents_mul (x y : RatFunc k) (hx : x ≠ 0) (hy : y ≠ 0) :
    exponents (x * y) (mul_ne_zero hx hy) = exponents x hx + exponents y hy := by
  ext p
  have he := valuation_eq_exp_neg_exponents p (x * y) (mul_ne_zero hx hy)
  rw [map_mul, valuation_eq_exp_neg_exponents p x hx,
    valuation_eq_exp_neg_exponents p y hy, ← WithZero.exp_add, WithZero.exp_inj] at he
  simp only [Finsupp.add_apply]
  omega

theorem exponents_inv (x : RatFunc k) (hx : x ≠ 0) :
    exponents x⁻¹ (inv_ne_zero hx) = -exponents x hx := by
  ext p
  have he := valuation_eq_exp_neg_exponents p x⁻¹ (inv_ne_zero hx)
  rw [map_inv₀, valuation_eq_exp_neg_exponents p x hx,
    ← WithZero.exp_neg, WithZero.exp_inj] at he
  simp only [Finsupp.neg_apply]
  omega

theorem exponents_div (x y : RatFunc k) (hx : x ≠ 0) (hy : y ≠ 0) :
    exponents (x / y) (div_ne_zero hx hy) = exponents x hx - exponents y hy := by
  simp only [div_eq_mul_inv, exponents_mul _ _ hx (inv_ne_zero hy), exponents_inv y hy,
    sub_eq_add_neg]

/-- The horizontal point X, used for the limit coordinate when retained. -/
def xPoint : MonicIrreducible k := ⟨X, monic_X, irreducible_X⟩

@[simp] theorem valuation_xPoint_X :
    valuation (xPoint (k := k)) RatFunc.X = WithZero.exp (-1 : ℤ) := by
  simpa only [PrincipalProfiles.factor, xPoint, RatFunc.algebraMap_X] using
    valuation_factor_self (xPoint (k := k))

theorem valuation_xPoint_polynomial (f : k[X]) (hf : f ≠ 0) :
    valuation (xPoint (k := k)) (algebraMap k[X] (RatFunc k) f) =
      WithZero.exp (-(f.natTrailingDegree : ℤ)) := by
  have h := PrimaryStabilization.valuation_eval₂_eq_pow_natTrailingDegree
    (valuation (xPoint (k := k))) RatFunc.C f hf RatFunc.X
    (by rw [valuation_xPoint_X]; exact WithZero.exp_pos)
    (by rw [valuation_xPoint_X, ← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num)
    (fun i hi => valuation_constant _ _ hi)
  change valuation (xPoint (k := k)) (aeval RatFunc.X f) = _ at h
  rw [RatFunc.aeval_X_left_eq_algebraMap, valuation_xPoint_X, ← WithZero.exp_nsmul] at h
  convert h using 1
  congr 1
  simp

/-- The X-coordinate is exactly the eventual primary order already used by the schedule. -/
theorem valuation_xPoint_eq_exp_neg_tOrder (x : RatFunc ℚ) (hx : x ≠ 0) :
    valuation (xPoint (k := ℚ)) x = WithZero.exp (-PrimaryStabilization.tOrder x) := by
  conv_lhs => rw [← RatFunc.num_div_denom x]
  rw [map_div₀, valuation_xPoint_polynomial x.num (RatFunc.num_ne_zero hx),
    valuation_xPoint_polynomial x.denom x.denom_ne_zero, ← WithZero.exp_sub]
  congr 1
  simp only [PrimaryStabilization.tOrder]
  omega

theorem exponent_xPoint_eq_tOrder (x : RatFunc ℚ) (hx : x ≠ 0) :
    exponents x hx (xPoint (k := ℚ)) = PrimaryStabilization.tOrder x := by
  have h := valuation_xPoint_eq_exp_neg_tOrder x hx
  rw [valuation_eq_exp_neg_exponents _ x hx, WithZero.exp_inj] at h
  exact neg_injective h

theorem retained_xPoint_of_constantCoeff_ne_zero (S : Set k[X])
    (hS : ∀ q ∈ S, q.coeff 0 ≠ 0) : Retained S (xPoint (k := k)) := by
  intro q hq hdvd
  exact hS q hq (Polynomial.X_dvd_iff.mp hdvd)

end
end UnconditionalCounterexample.HorizontalOrders
