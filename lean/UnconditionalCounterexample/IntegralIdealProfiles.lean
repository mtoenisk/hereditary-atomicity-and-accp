import UnconditionalCounterexample.FractionalIdealProfiles
import UnconditionalCounterexample.RadicalIdealProducts

/-!
# Integral ideals from attained nonnegative fractional profiles

A nonnegative actual fractional-ideal profile gives containment in the full
valuation intersection, hence an ordinary integral ideal. An attained natural
profile value identifies its maximal localization using the proved principal
local-power dictionary. No finite-generation assumption is needed in either
conversion.
-/

noncomputable section
namespace UnconditionalCounterexample.IntegralIdealProfiles
open WithZero FractionalIdealProfiles RadicalIdealProducts
open scoped nonZeroDivisors
variable {R K : Type*} [CommRing R] [Field K] [Algebra R K]

/-- Every nonnegative actual profile defines an integral ideal of the full
intersection, with exact equality of the embedded fractional ideals. -/
theorem exists_integral_ideal {ι : Type*} (v : ι → Valuation K ℤᵐ⁰)
    (hfull : ∀ x : K, x ∈ (1 : FractionalIdeal R⁰ K) ↔ ∀ i, v i x ≤ 1)
    (I : FractionalIdeal R⁰ K) (f : ι → ℤ) (hI : HasProfile v I f)
    (hf : ∀ i, 0 ≤ f i) : ∃ J : Ideal R, (J : FractionalIdeal R⁰ K) = I := by
  apply FractionalIdeal.le_one_iff_exists_coeIdeal.mp
  intro x hx
  apply (hfull x).mpr
  intro i
  exact ((hI i).1 x hx).trans (exp_le_one_iff.mpr (neg_nonpos.mpr (hf i)))

/-- An attained actual ideal value is its true local exponent, using only the
normalized principal-order law and the minimum over all nonzero ideal members. -/
theorem localIdeal_eq_pow_of_hasValue (v : Maximal R → Valuation K ℤᵐ⁰)
    (ν : Maximal R → R → ℕ)
    (hvalue : ∀ (M : Maximal R) (x : R), x ≠ 0 →
      v M (algebraMap R K x) = exp (-(ν M x : ℤ)))
    (hprincipal : ∀ (M : Maximal R) (x : R), x ≠ 0 →
      localIdeal M (Ideal.span {x}) = localMaximal M ^ ν M x)
    (J : Ideal R) (M : Maximal R) (n : ℕ)
    (hJ : HasValue (J : FractionalIdeal R⁰ K) (v M) (n : ℤ)) :
    localIdeal M J = localMaximal M ^ n := by
  have hJ0 : J ≠ ⊥ := by
    intro hzero
    exact hJ.ne_zero (by simp [hzero])
  have hmin : minimum ν J M = n := by
    apply le_antisymm
    · obtain ⟨y, hy, hvy⟩ := hJ.2
      obtain ⟨x, hx, rfl⟩ := (FractionalIdeal.mem_coeIdeal R⁰).mp hy
      have hx0 : x ≠ 0 := by
        intro hz
        simp only [hz, map_zero] at hvy
        exact exp_ne_zero hvy.symm
      have he := exp_injective ((hvalue M x hx0).symm.trans hvy)
      have he' : ν M x = n := by omega
      exact (minimum_le ν J M ⟨x, hx, hx0⟩).trans_eq he'
    · obtain ⟨x, hx⟩ := minimum_attained ν J hJ0 M
      have h := hJ.1 (algebraMap R K x)
        ((FractionalIdeal.mem_coeIdeal R⁰).mpr ⟨x, x.property.1, rfl⟩)
      rw [hvalue M x x.property.2, exp_le_exp] at h
      omega
  rw [localIdeal_eq_pow_minimum ν hprincipal J hJ0 M, hmin]

end UnconditionalCounterexample.IntegralIdealProfiles
