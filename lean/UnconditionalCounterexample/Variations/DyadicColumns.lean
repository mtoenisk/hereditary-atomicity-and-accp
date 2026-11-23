import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Integral elimination for a dyadic valuation channel

After removing horizontal and guard coordinates, each channel consists of
finitely supported integer sequences at the plus and minus sites and a finite
auxiliary part. The kernel of its signed rational mass has unique integral
coordinates in the balanced, adjacent and auxiliary columns of the dyadic profile construction.
-/

noncomputable section

namespace UnconditionalCounterexample.DyadicColumns

/-- The mass of finitely many entries with weights `2^(-n-1)`. -/
def mass : (ℕ →₀ ℤ) →+ ℚ :=
  Finsupp.liftAddHom fun n => zmultiplesHom ℚ ((1 / 2 : ℚ) ^ (n + 1))

theorem mass_single (n : ℕ) (z : ℤ) :
    mass (Finsupp.single n z) = (z : ℚ) * (1 / 2 : ℚ) ^ (n + 1) := by
  simp [mass, zsmul_eq_mul]

/-- Sum of adjacent columns `Q_n = -e_n + 2 e_(n+1)` with the given exponents. -/
def adjacent : (ℕ →₀ ℤ) →+ (ℕ →₀ ℤ) :=
  (2 : ℕ) • Finsupp.mapDomain.addMonoidHom Nat.succ - AddMonoidHom.id _

theorem adjacent_zero (q : ℕ →₀ ℤ) : adjacent q 0 = - q 0 := by
  change (2 : ℕ) • (Finsupp.mapDomain Nat.succ q) 0 - q 0 = _
  rw [Finsupp.mapDomain_of_notMem_range _ _ (by simp)]
  simp

theorem adjacent_succ (q : ℕ →₀ ℤ) (n : ℕ) :
    adjacent q (n+1) = 2 * q n - q (n+1) := by
  change (2 : ℕ) • Finsupp.mapDomain Nat.succ q (Nat.succ n) - q (n+1) = _
  rw [Finsupp.mapDomain_apply_of_injective Nat.succ_injective]
  simp

theorem mass_adjacent (q : ℕ →₀ ℤ) : mass (adjacent q) = 0 := by
  induction q using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | single n z =>
    change mass ((2 : ℕ) • Finsupp.mapDomain Nat.succ (Finsupp.single n z) -
      Finsupp.single n z) = 0
    rw [Finsupp.mapDomain_single, map_sub, map_nsmul, mass_single, mass_single, pow_succ]
    ring

/-- The carry before processing entry `n`. Its successor is the exponent of `Q_n`. -/
private def carry (d : ℕ →₀ ℤ) : ℕ → ℤ
  | 0 => 0
  | n+1 => 2 * carry d n - d n

private theorem prefix_mass (d : ℕ →₀ ℤ) (n : ℕ) :
    ∑ i ∈ Finset.range n, (d i : ℚ) * (1 / 2 : ℚ) ^ (i + 1) =
      - (carry d n : ℚ) * (1 / 2 : ℚ) ^ n := by
  induction n with
  | zero => simp [carry]
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, carry, pow_succ]
    push_cast
    ring

private theorem mass_eq_prefix (d : ℕ →₀ ℤ) (n : ℕ) (hs : d.support ⊆ Finset.range n) :
    mass d = ∑ i ∈ Finset.range n, (d i : ℚ) * (1 / 2 : ℚ) ^ (i+1) := by
  change d.sum (fun i z => z • ((1 / 2 : ℚ) ^ (i+1))) = _
  rw [Finsupp.sum_of_support_subset _ hs _ (by simp)]
  simp [zsmul_eq_mul]

private theorem carry_zero_of_support (d : ℕ →₀ ℤ) (hd : mass d = 0) (n : ℕ)
    (hs : d.support ⊆ Finset.range n) : carry d n = 0 := by
  rw [mass_eq_prefix d n hs, prefix_mass] at hd
  have hz : - (carry d n : ℚ) = 0 :=
    (mul_eq_zero.mp hd).resolve_right (pow_ne_zero _ (by norm_num))
  exact_mod_cast neg_eq_zero.mp hz

/-- A finite mass is an integral multiple of one arbitrarily late site's weight. -/
theorem mass_eq_multiple_of_late_weight (d : ℕ →₀ ℤ) (L : ℕ) :
    ∃ n ≥ L, ∃ z : ℤ, mass d = (z : ℚ) * (1 / 2 : ℚ) ^ (n+1) := by
  let n := max L (d.support.sup id)
  have hs : d.support ⊆ Finset.range (n+1) := by
    intro i hi
    have hb : i ≤ d.support.sup id := Finset.le_sup (f := id) hi
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (hb.trans (Nat.le_max_right _ _)))
  refine ⟨n, Nat.le_max_left _ _, -carry d (n+1), ?_⟩
  rw [mass_eq_prefix d (n+1) hs, prefix_mass, Int.cast_neg]

theorem adjacent_injective : Function.Injective adjacent := by
  intro q q' h
  ext n
  induction n with
  | zero => simpa only [adjacent_zero, neg_inj] using DFunLike.congr_fun h 0
  | succ n ih =>
    have he := DFunLike.congr_fun h (n+1)
    simp only [adjacent_succ, ih] at he
    omega

/-- The adjacent coefficients can be recovered from a finite prefix. If all
discrepancies occur through index `N`, the last possible adjacent generator
is `Q_(N-1)`. In particular an elimination never needs a later raw. -/
theorem adjacent_support_lt (q : ℕ →₀ ℤ) (N : ℕ)
    (hs : (adjacent q).support ⊆ Finset.range (N+1)) : q.support ⊆ Finset.range N := by
  have hc (n : ℕ) : carry (adjacent q) (n+1) = q n := by
    induction n with
    | zero => simp [carry, adjacent_zero]
    | succ n ih => rw [carry, ih, adjacent_succ]; omega
  intro n hn
  by_contra h
  have hN : N ≤ n := by simpa using h
  have hs' : (adjacent q).support ⊆ Finset.range (n+1) :=
    hs.trans (Finset.range_mono (by omega))
  exact (Finsupp.mem_support_iff.mp hn)
    ((hc n).symm.trans (carry_zero_of_support _ (mass_adjacent _) _ hs'))

/-- The adjacent columns are an integral basis of the kernel of regular mass. -/
theorem mass_eq_zero_iff_existsUnique_adjacent (d : ℕ →₀ ℤ) :
    mass d = 0 ↔ ∃! q, adjacent q = d := by
  constructor
  · intro hd
    let m := d.support.sup id
    have hs (n : ℕ) (hn : m ≤ n) : d.support ⊆ Finset.range (n+1) := by
      intro i hi
      have hi' : i ≤ m := Finset.le_sup (f := id) hi
      exact Finset.mem_range.mpr (by omega)
    let q : ℕ →₀ ℤ := Finsupp.onFinset (Finset.range m) (fun n => carry d (n+1)) (by
      intro n hn
      by_contra hg
      exact hn (carry_zero_of_support d hd _ (hs n (by simpa using hg))))
    have hq : adjacent q = d := by
      ext n
      cases n with
      | zero => simp [adjacent_zero, q, carry]
      | succ n =>
        rw [adjacent_succ]
        change 2 * carry d (n+1) - (2 * carry d (n+1) - d (n+1)) = d (n+1)
        omega
    exact ⟨q, hq, fun y hy => adjacent_injective (hy.trans hq.symm)⟩
  · rintro ⟨q, rfl, _⟩
    exact mass_adjacent _

/-- Transferring auxiliary entry `z_j` to the regular plus coordinate contributes
`σ_j z_j` at its index. This describes subtraction of the auxiliary column
`S_j = e_j - σ_j e⁺_(index j)`. In the construction the signs are ±1. -/
def auxiliaryTransfer {J : Type*} (index : J → ℕ) (sign : J → ℤ) :
    (J →₀ ℤ) →+ (ℕ →₀ ℤ) :=
  Finsupp.liftAddHom fun j => (Finsupp.singleAddHom (index j)).comp
    (zmultiplesHom ℤ (sign j))

theorem mass_auxiliaryTransfer {J : Type*} (index : J → ℕ) (sign : J → ℤ)
    (z : J →₀ ℤ) : mass (auxiliaryTransfer index sign z) =
      z.sum (fun j v => ((v * sign j : ℤ) : ℚ) * (1 / 2 : ℚ) ^ (index j+1)) := by
  classical
  simp only [auxiliaryTransfer, Finsupp.liftAddHom_apply, Finsupp.sum, map_sum,
    AddMonoidHom.comp_apply, zmultiplesHom_apply, zsmul_eq_mul,
    Finsupp.singleAddHom_apply, mass_single, Int.cast_id]

/-- In one channel, the exponents of the balanced columns `R_n` are the
minus entries `b`, and the exponents of the auxiliary columns `S_j` are the
auxiliary entries `z`. Zero signed mass is precisely the condition for the
remaining plus entries to come from unique integral exponents of the `Q_n`. -/
theorem signed_mass_eq_zero_iff_columns {J : Type*} (index : J → ℕ) (sign : J → ℤ)
    (a b : ℕ →₀ ℤ) (z : J →₀ ℤ) :
    mass a - mass b +
      z.sum (fun j v => ((v * sign j : ℤ) : ℚ) * (1 / 2 : ℚ) ^ (index j+1)) = 0 ↔
    ∃! q : ℕ →₀ ℤ, a = b + adjacent q - auxiliaryTransfer index sign z := by
  rw [← mass_auxiliaryTransfer, ← map_sub, ← map_add, mass_eq_zero_iff_existsUnique_adjacent]
  apply existsUnique_congr
  intro q
  constructor <;> intro h <;> rw [h] <;> abel

end UnconditionalCounterexample.DyadicColumns
