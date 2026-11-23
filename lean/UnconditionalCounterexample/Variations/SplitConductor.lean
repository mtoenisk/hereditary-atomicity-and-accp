import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.LinearCombination
import UnconditionalCounterexample.ConductorAtomicity

/-!
# Splitting inside a subring containing an integer conductor

The splitting construction assigns every fibre over a prime divisor of the conductor
to one of the two factors. This allows different unit congruences for the
two factors. The resulting bounded factors belong to the original subring.
-/

namespace UnconditionalCounterexample.DyadicSplit

variable {D : Type*} [CommRing D]

/-- Patch two representatives in a subring at coprime parts of its conductor. -/
theorem mem_subring_of_coprime_congruences (T : Subring D) {a b : ℕ} (hab : a.Coprime b)
    (hc : ∀ z : D, ((a * b : ℕ) : D) * z ∈ T) {u v w : D}
    (hv : v ∈ T) (hw : w ∈ T) (ha : (a : D) ∣ u - v) (hb : (b : D) ∣ u - w) :
    u ∈ T := by
  obtain ⟨i, j, hij⟩ := hab.isCoprime
  have hone : (i : D) * a + (j : D) * b = 1 := by
    simpa using congrArg (Int.castRingHom D) hij
  obtain ⟨s, hs⟩ := ha
  obtain ⟨t, ht⟩ := hb
  have hrep : ((i : D) * a) * w + ((j : D) * b) * v ∈ T :=
    T.add_mem (T.mul_mem (T.mul_mem (intCast_mem T i) (natCast_mem T a)) hw)
      (T.mul_mem (T.mul_mem (intCast_mem T j) (natCast_mem T b)) hv)
  have heq : u = ((i : D) * a) * w + ((j : D) * b) * v +
      ((a * b : ℕ) : D) * ((i : D) * t + (j : D) * s) := by
    calc
      u = ((i : D) * a + (j : D) * b) * u := by rw [hone, one_mul]
      _ = ((i : D) * a) * w + ((j : D) * b) * v +
          (((i : D) * a) * (u-w) + ((j : D) * b) * (u-v)) := by ring
      _ = _ := by rw [hs, ht, Nat.cast_mul]; ring
  exact heq ▸ T.add_mem hrep (hc _)

/-- If each prime-power fibre is assigned wholly to one factor, their
product's membership places both factors in the same subring. This also
covers the vacuous congruences at conductor one. -/
theorem factors_mem_of_coprime_returns (T : Subring D) {a b : ℕ} (hab : a.Coprime b)
    (hc : ∀ z : D, ((a * b : ℕ) : D) * z ∈ T)
    {u v : D} (hx : u * v ∈ T) (hu : (a : D) ∣ u - 1) (hv : (b : D) ∣ v - 1) :
    u ∈ T ∧ v ∈ T := by
  have hu' : (b : D) ∣ u - u * v := by
    obtain ⟨t, ht⟩ := hv
    exact ⟨-(u*t), by linear_combination -u * ht⟩
  have hv' : (a : D) ∣ v - u * v := by
    obtain ⟨s, hs⟩ := hu
    exact ⟨-(v*s), by linear_combination -v * hs⟩
  exact ⟨mem_subring_of_coprime_congruences T hab hc T.one_mem hx hu hu',
    mem_subring_of_coprime_congruences T hab hc hx T.one_mem hv' hv⟩

variable [IsDomain D]

/-- The two-axis hereditary atomicity argument. The construction must supply
the integer conductor, the bounds on the axes, and the simultaneous
ambient split with whole-fibre congruences. -/
theorem hereditarilyAtomic_of_axis_splits
    (r s : D → ℕ)
    (hindex : ∀ T : Subring D, ¬ Factorization.IsBFDomain T →
      ∃ m : ℕ, 0 < m ∧ ∀ z : D, (m : D) * z ∈ T)
    (haxis : ∀ (T : Subring D) (x : T), x ≠ 0 → r x = 0 ∨ s x = 0 →
      Factorization.HasBoundedFactorizations x)
    (hsplit : ∀ (x : D) (m : ℕ), x ≠ 0 → 0 < m → 0 < r x → 0 < s x →
      ∃ (u v : D) (a b : ℕ), x = u * v ∧ s u = 0 ∧ r v = 0 ∧ m = a * b ∧
        a.Coprime b ∧ (a : D) ∣ u - 1 ∧ (b : D) ∣ v - 1) :
    Factorization.IsHereditarilyAtomic D := by
  intro T
  by_cases hBF : Factorization.IsBFDomain T
  · exact hBF.isAtomicDomain
  obtain ⟨m, hm, hc⟩ := hindex T hBF
  intro x hx
  by_cases hz : r x = 0 ∨ s x = 0
  · exact (haxis T x hx hz).hasAtomicFactorization
  have hxD : (x : D) ≠ 0 := fun h => hx (Subtype.ext h)
  obtain ⟨u, v, a, b, huv, hu, hv, rfl, hab, hua, hvb⟩ :=
    hsplit x m hxD hm (by omega) (by omega)
  obtain ⟨huT, hvT⟩ := factors_mem_of_coprime_returns T hab hc (huv ▸ x.property) hua hvb
  let uT : T := ⟨u, huT⟩
  let vT : T := ⟨v, hvT⟩
  have hprod : x = uT * vT := Subtype.ext huv
  have hp0 : uT * vT ≠ 0 := hprod ▸ hx
  rw [hprod]
  exact ((haxis T uT (left_ne_zero_of_mul hp0) (Or.inr hu)).hasAtomicFactorization).mul
    ((haxis T vT (right_ne_zero_of_mul hp0) (Or.inl hv)).hasAtomicFactorization)

end UnconditionalCounterexample.DyadicSplit
