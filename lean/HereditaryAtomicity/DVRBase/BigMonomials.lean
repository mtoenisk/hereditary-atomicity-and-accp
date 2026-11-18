import HereditaryAtomicity.ConductorBranches
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset

/-!
# Actual return of large specified monomials

A sufficiently large monomial contains a prescribed power of one of the chain ratios.
Divisibility in the source ring then proves membership there (semilocal Lemma 5.3).
-/

noncomputable section
namespace HereditaryAtomicity.DVRBase
open scoped BigOperators

variable {ι : Type*} [Fintype ι]

/-- Above the degree cutoff, either the coefficient exponent clears the denominator or the
exponent of a variable reaches its power-return threshold. -/
theorem large_monomial_exponent_alternative
    (κ e : ℕ) (n q : ι → ℕ) (u : ι → ℝ)
    (hu0 : ∀ i, 0 ≤ u i) (huκ : ∀ i, u i ≤ κ)
    (hlarge : 2 * (κ : ℝ) * (∑ i, (n i : ℝ)) ≤
      (e : ℝ) - κ + ∑ i, (q i : ℝ) * u i) :
    κ ≤ e ∨ ∃ i, n i ≤ q i := by
  by_cases hκe : κ ≤ e
  · exact Or.inl hκe
  right
  by_contra hnq
  have hq : ∀ i, q i ≤ n i := by
    intro i
    have : ¬ n i ≤ q i := fun h => hnq ⟨i, h⟩
    omega
  have hsum : (∑ i, (q i : ℝ) * u i) ≤ (κ : ℝ) * ∑ i, (n i : ℝ) := by
    calc
      _ ≤ ∑ i, (n i : ℝ) * (κ : ℝ) := by
        apply Finset.sum_le_sum
        intro i _
        exact mul_le_mul (by exact_mod_cast hq i) (huκ i) (hu0 i) (Nat.cast_nonneg _)
      _ = _ := by rw [← Finset.sum_mul]; ring
  have heκ : (e : ℝ) < κ := by exact_mod_cast (Nat.lt_of_not_ge hκe)
  have hnonneg : 0 ≤ (κ : ℝ) * ∑ i, (n i : ℝ) := by positivity
  linarith

/-- The required return is divisibility inside the source ring itself. -/
theorem large_monomial_numerator_dvd
    {R : Type*} [CommRing R] (π : R) (y : ι → R)
    (κ e : ℕ) (n q : ι → ℕ) (u : ι → ℝ)
    (hreturn : ∀ i, π ^ κ ∣ y i ^ n i)
    (hu0 : ∀ i, 0 ≤ u i) (huκ : ∀ i, u i ≤ κ)
    (hlarge : 2 * (κ : ℝ) * (∑ i, (n i : ℝ)) ≤
      (e : ℝ) - κ + ∑ i, (q i : ℝ) * u i) :
    π ^ κ ∣ π ^ e * ∏ i, y i ^ q i := by
  rcases large_monomial_exponent_alternative κ e n q u hu0 huκ hlarge with he | ⟨i, hi⟩
  · exact dvd_mul_of_dvd_left (pow_dvd_pow π he) _
  · have hd : π ^ κ ∣ ∏ j, y j ^ q j :=
      (hreturn i).trans ((pow_dvd_pow (y i) hi).trans
        (Finset.dvd_prod_of_mem (fun j => y j ^ q j) (Finset.mem_univ i)))
    exact dvd_mul_of_dvd_right hd _

/-- A large specified Laurent monomial belongs to the literal source subring,
provided the prescribed variable-power quotients already belong there. -/
theorem large_monomial_mem_source
    {K : Type*} [Field K] (A : Subring K) (π : A) (hπ0 : π ≠ 0)
    (y : ι → A) (κ e : ℕ) (n q : ι → ℕ) (u : ι → ℝ)
    (hreturn : ∀ i, (y i : K) ^ n i / (π : K) ^ κ ∈ A)
    (hu0 : ∀ i, 0 ≤ u i) (huκ : ∀ i, u i ≤ κ)
    (hlarge : 2 * (κ : ℝ) * (∑ i, (n i : ℝ)) ≤
      (e : ℝ) - κ + ∑ i, (q i : ℝ) * u i) :
    (π : K) ^ e / (π : K) ^ κ * ∏ i, (y i : K) ^ q i ∈ A := by
  have hpK : (π : K) ^ κ ≠ 0 := pow_ne_zero _ (Subtype.coe_ne_coe.mpr hπ0)
  have hdiv : ∀ i, π ^ κ ∣ y i ^ n i := by
    intro i
    refine ⟨⟨_, hreturn i⟩, ?_⟩
    apply Subtype.ext
    change (y i : K) ^ n i = (π : K) ^ κ * ((y i : K) ^ n i / (π : K) ^ κ)
    exact (mul_div_cancel₀ _ hpK).symm
  obtain ⟨a, ha⟩ := large_monomial_numerator_dvd π y κ e n q u hdiv hu0 huκ hlarge
  have haK : (π : K) ^ e * ∏ i, (y i : K) ^ q i = (π : K) ^ κ * (a : K) := by
    simpa only [map_mul, map_pow, map_prod, Subring.subtype_apply] using
      congrArg A.subtype ha
  have heq : (π : K) ^ e / (π : K) ^ κ * ∏ i, (y i : K) ^ q i = (a : K) := by
    rw [div_mul_eq_mul_div, haK, mul_div_cancel_left₀ _ hpK]
  rw [heq]
  exact a.property

end HereditaryAtomicity.DVRBase
