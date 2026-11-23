import UnconditionalCounterexample.Variations.MultiDomain
import Mathlib.Data.Int.GCD

/-!
# Rational scalar units at the guards

A normalized guard over every rational prime detects every denominator.
Bézout's identity for a reduced numerator and denominator proves this for
arbitrary guard fields.
-/

noncomputable section
namespace UnconditionalCounterexample.Variations.MultiDomain

open WithZero GuardSupport IntersectionDomain

variable {K : Type*} [Field K] [CharZero K]

omit [CharZero K] in
private theorem int_le (v : Valuation K ℤᵐ⁰) (z : ℤ) : v (z : K) ≤ 1 := by
  exact (show (z : K) ∈ v.valuationSubring from intCast_mem v.valuationSubring z)

theorem integer_of_guard_integral (g : PrimeIndex → Valuation K ℤᵐ⁰)
    (hg : ∀ p, g p (p.val : K) < 1) (c : ℚ) (hc : ∀ p, g p (c : K) ≤ 1) :
    ∃ z : ℤ, (z : ℚ) = c := by
  refine ⟨c.num, (Rat.den_eq_one_iff c).mp ?_⟩
  by_contra hden
  obtain ⟨p, hp, m, hm⟩ := Nat.exists_prime_and_dvd hden
  let v := g ⟨p,hp⟩
  have hd : v (c.den : K) < 1 := by
    rw [hm, Nat.cast_mul, map_mul]
    calc
      _ ≤ v (p : K) * 1 := mul_le_mul_of_nonneg_left (valuation_natCast_le_one v m) zero_le
      _ < 1 := by simpa [v] using hg ⟨p,hp⟩
  have hn : v (c.num : K) < 1 := by
    have he : (c : K) * (c.den : K) = (c.num : K) := by exact_mod_cast Rat.mul_den_eq_num c
    rw [← he, map_mul]
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right (hc ⟨p,hp⟩) zero_le) (by simpa using hd)
  have he : (1 : ℤ) = c.num * Int.gcdA c.num c.den + (c.den : ℤ) * Int.gcdB c.num c.den := by
    have he := Int.gcd_eq_gcd_ab c.num c.den
    simpa [Int.gcd, c.reduced.gcd_eq_one] using he
  have heK := congrArg (Int.castRingHom K) he
  simp only [map_one, map_add, map_mul, Int.coe_castRingHom, Int.cast_natCast] at heK
  have hlt (x : K) (hx : v x < 1) (z : ℤ) : v (x * (z : K)) < 1 := by
    rw [map_mul]
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left (int_le v z) zero_le) (by simpa using hx)
  have h := (v.map_add _ _).trans_lt (max_lt (hlt _ hn (Int.gcdA c.num c.den)) (hlt _ hd (Int.gcdB c.num c.den)))
  rw [← heK, map_one] at h
  exact lt_irrefl _ h

theorem sign_of_guard_units (g : PrimeIndex → Valuation K ℤᵐ⁰)
    (hg : ∀ p, g p (p.val : K) < 1) (c : ℚ) (hc : ∀ p, g p (c : K) = 1) :
    c = 1 ∨ c = -1 := by
  have hc₀ : c ≠ 0 := by
    rintro rfl
    simpa using hc ⟨2,Nat.prime_two⟩
  obtain ⟨a, ha⟩ := integer_of_guard_integral g hg c (fun p ↦ (hc p).le)
  obtain ⟨b, hb⟩ := integer_of_guard_integral g hg c⁻¹ (fun p ↦ by simp [Rat.cast_inv, map_inv₀, hc])
  have hab : a*b = 1 := by exact_mod_cast (show (a:ℚ)*(b:ℚ) = 1 by rw [ha, hb, mul_inv_cancel₀ hc₀])
  rcases Int.isUnit_iff.mp (isUnit_iff_exists_inv.mpr ⟨b, hab⟩) with h | h
  · exact Or.inl (by simpa [h] using ha.symm)
  · exact Or.inr (by simpa [h] using ha.symm)

end UnconditionalCounterexample.Variations.MultiDomain
