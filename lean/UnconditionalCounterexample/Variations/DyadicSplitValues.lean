import UnconditionalCounterexample.Variations.UnivariateValues
import Mathlib.Data.Nat.Factorization.Basic

/-!
# Relative targets at the reserved balanced raw

At every prime dividing the prescribed modulus the entire fibre is assigned
to one factor. The last raw occurs once, so its normalized target is the
quotient of the desired local value by the previously fixed factor. The actual
relative precision from the polynomial selector suffices even when the
dividend is a nonunit at that fibre.
-/

noncomputable section

namespace UnconditionalCounterexample.DyadicSplit

open GuardSupport PrimaryChoices CombinedGuardStep MixedStageSelection
open Variations.Univariate

set_option backward.isDefEq.respectTransparency false

/-- True indicates that the entire fibre has been assigned to the first factor. -/
def reservedTarget {K : Type*} [Field K] (first : Bool) (x u₀ : K) : K :=
  (if first then x else 1) / u₀

theorem reservedTarget_ne_zero {K : Type*} [Field K] (first : Bool) {x u₀ : K}
    (hx : x ≠ 0) (h₀ : u₀ ≠ 0) : reservedTarget first x u₀ ≠ 0 := by
  cases first <;> simp [reservedTarget, hx, h₀]

variable {p : ℕ} [Fact p.Prime]

private theorem reservedTarget_norm (first : Bool) {x u₀ : ℚ_[p]} (h₀ : u₀ ≠ 0)
    (hmatch : ‖u₀‖ = if first then ‖x‖ else 1) :
    ‖reservedTarget first x u₀‖ = 1 := by
  rw [reservedTarget, norm_div, ← div_self (norm_ne_zero_iff.mpr h₀)]
  congr 1
  cases first <;> simpa using hmatch.symm

/-- Matching the order already assigned to the earlier factors means that
the newly prescribed target is an actual p-adic unit. -/
theorem reservedTarget_unit (first : Bool) {x u₀ : ℚ_[p]} (h₀ : u₀ ≠ 0)
    (hmatch : ‖u₀‖ = if first then ‖x‖ else 1) :
    ∃ t : ℤ_[p]ˣ, (t.val : ℚ_[p]) = reservedTarget first x u₀ := by
  have hnorm := reservedTarget_norm first h₀ hmatch
  let t : ℤ_[p] := ⟨reservedTarget first x u₀, hnorm.le⟩
  have ht : IsUnit t := PadicInt.isUnit_iff.mpr hnorm
  exact ⟨ht.unit, congrArg Subtype.val ht.unit_spec⟩

private theorem mul_complement_error {u v d : ℚ_[p]} (hu : u ∈ PadicInt.subring p)
    (hv : (v-1)/d ∈ PadicInt.subring p) : (u-u*v)/d ∈ PadicInt.subring p := by
  rw [show (u-u*v)/d = -(u*((v-1)/d)) by ring]
  exact (PadicInt.subring p).neg_mem ((PadicInt.subring p).mul_mem hu hv)

/-- For the actual normalized raw `g`, both factors have the assigned
congruences modulo the full prime power. The old factor's exponent on `g`
is exactly one, as in the reserved-column computation. -/
theorem factor_congruences (first : Bool) (x u₀ g : ℚ_[p]) (k : ℕ)
    (hx : x ≠ 0) (h₀ : u₀ ≠ 0) (hint : x ∈ PadicInt.subring p)
    (hmatch : ‖u₀‖ = if first then ‖x‖ else 1)
    (hg : ‖g‖ = ‖reservedTarget first x u₀‖)
    (hprec : (reservedTarget first x u₀ / g - 1) / (p : ℚ_[p]) ^ k ∈ PadicInt.subring p) :
    let u := u₀*g
    let v := x/u
    (u - (if first then x else 1)) / (p : ℚ_[p]) ^ k ∈ PadicInt.subring p ∧
      (v - (if first then 1 else x)) / (p : ℚ_[p]) ^ k ∈ PadicInt.subring p := by
  dsimp only
  have hgne : g ≠ 0 := norm_ne_zero_iff.mp
    (hg.symm ▸ norm_ne_zero_iff.mpr (reservedTarget_ne_zero first hx h₀))
  let u := u₀*g
  let v := x/u
  have hu0 : u ≠ 0 := mul_ne_zero h₀ hgne
  have huv : u*v = x := mul_div_cancel₀ _ hu0
  have hunorm : ‖u‖ = if first then ‖x‖ else 1 := by
    change ‖u₀*g‖ = _
    rw [norm_mul, hg, reservedTarget_norm first h₀ hmatch, mul_one, hmatch]
  have hxnorm : ‖x‖ ≤ 1 := hint
  cases first
  · simp only [Bool.false_eq_true, ↓reduceIte] at hunorm ⊢
    have hu : u ∈ PadicInt.subring p := hunorm.le
    have hv : v ∈ PadicInt.subring p := by
      change ‖v‖ ≤ 1
      simpa [v, norm_div, hunorm] using hxnorm
    have hret : (u⁻¹ - 1) / (p : ℚ_[p]) ^ k ∈ PadicInt.subring p := by
      have he : reservedTarget false x u₀ / g = u⁻¹ := by
        simp [reservedTarget, u, div_eq_mul_inv, mul_comm]
      rwa [he] at hprec
    have hret' := mul_complement_error hu hret
    rw [mul_inv_cancel₀ hu0] at hret'
    exact ⟨hret', by simpa only [mul_comm v u, huv] using mul_complement_error hv hret'⟩
  · simp only [↓reduceIte] at hunorm ⊢
    have hu : u ∈ PadicInt.subring p := hunorm.trans_le hxnorm
    have he : reservedTarget true x u₀ / g = v := by
      simp [reservedTarget, v, u, div_div]
    rw [he] at hprec
    exact ⟨huv ▸ mul_complement_error hu hprec, hprec⟩

/-- Evaluation at a processed branch. Inactive selectors receive the unused
value one. -/
def branchValue {p : PrimeIndex} (site : Site p) (b : Bool) (x : RatFunc ℚ) : ℚ_[p.val] := by
  classical
  exact if hb : Active site.paired b then site.evaluate b hb x else 1

theorem branchValue_ne_zero {p : PrimeIndex} (site : Site p) (b : Bool)
    {x : RatFunc ℚ} (hx : x ≠ 0) : branchValue site b x ≠ 0 := by
  unfold branchValue
  split
  · exact (map_ne_zero _).mpr hx
  · exact one_ne_zero

/-- Overlay a split task on the batch's ordinary column targets. At a prime
dividing the modulus, all active branches use the same assignment and the
full exponent of that prime in the modulus. -/
def reserveTargets (B : Batch) (sites : Table B.assigned.primes) (base : Targets B sites)
    (m : ℕ) (first : ℕ → Bool) (x u₀ : RatFunc ℚ) (hx : x ≠ 0) (h₀ : u₀ ≠ 0) : Targets B sites where
  value i b := if B.primeAt i ∣ m then reservedTarget (first (B.primeAt i))
    (branchValue (siteAt B sites i) b x) (branchValue (siteAt B sites i) b u₀) else base.value i b
  precision i b := if B.primeAt i ∣ m then m.factorization (B.primeAt i) else base.precision i b
  nonzero i b hb := by
    split
    · exact reservedTarget_ne_zero _ (branchValue_ne_zero _ _ hx) (branchValue_ne_zero _ _ h₀)
    · exact base.nonzero i b hb

/-- At a literal selection stage using the split targets, both local
congruences hold for the factors built from the same global normalized raw. -/
theorem selected_factor_congruences (R : Requirements) (n m : ℕ) (first : ℕ → Bool)
    (x u₀ : RatFunc ℚ) (hx : x ≠ 0) (h₀ : u₀ ≠ 0)
    (base : Targets (selection R n).batch
      (extend R ((chain R).approx n) (table R n) (selection R n).batch))
    (ht : actualTargets R n = reserveTargets _ _ base m first x u₀ hx h₀)
    (i : (selection R n).batch.indices) (hi : (primes i.val).val ∣ m) (b : Bool)
    (hb : Active (permanentSite R (primes i.val)).paired b)
    (hint : (permanentSite R (primes i.val)).evaluate b hb x ∈ PadicInt.subring (primes i.val).val)
    (hmatch : ‖(permanentSite R (primes i.val)).evaluate b hb u₀‖ =
      if first (primes i.val).val then ‖(permanentSite R (primes i.val)).evaluate b hb x‖ else 1) :
    let p := (primes i.val).val
    let f := (permanentSite R (primes i.val)).evaluate b hb
    let u := u₀*(chain R).generators n
    let v := x/u
    (f u - (if first p then f x else 1)) / (p : ℚ_[p]) ^ m.factorization p ∈ PadicInt.subring p ∧
      (f v - (if first p then 1 else f x)) / (p : ℚ_[p]) ^ m.factorization p ∈ PadicInt.subring p := by
  obtain ⟨hg, he⟩ := processed_value R n i b hb
  have hv : (actualTargets R n).value i b = reservedTarget (first (primes i.val).val)
      ((permanentSite R (primes i.val)).evaluate b hb x)
      ((permanentSite R (primes i.val)).evaluate b hb u₀) := by
    have hi' : (selection R n).batch.primeAt i ∣ m := hi
    rw [ht]
    simp only [reserveTargets, ite_eq_left hi']
    change reservedTarget _ (branchValue (selectionSite R n i) b x)
      (branchValue (selectionSite R n i) b u₀) = _
    rw [selectionSite_eq]
    simp only [branchValue, dite_eq_left hb]
    rfl
  have hk : (actualTargets R n).precision i b = m.factorization (primes i.val).val := by
    rw [ht]
    exact ite_eq_left hi
  dsimp only at hg he ⊢
  rw [hv] at hg he
  rw [hk] at he
  simpa only [map_mul, map_div₀] using factor_congruences (first (primes i.val).val)
    _ _ _ _ ((map_ne_zero _).mpr hx) ((map_ne_zero _).mpr h₀) hint hmatch hg he

end UnconditionalCounterexample.DyadicSplit
