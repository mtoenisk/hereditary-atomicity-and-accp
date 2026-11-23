import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# The two regular dyadic mass equations

For profiles supported on the regular sites and the two centres, the signed
masses are finite rational computations. A common subprofile of the two
witnesses has mass at most one quarter in both channels. The principal-profile
equations then force both heights to be zero, leaving room at every sufficiently
late index for a balanced column.
-/

namespace UnconditionalCounterexample.DyadicProfiles

/-- Total weight on the indices starting at `n`. -/
def tailWeight (n : ℕ) : ℚ := (1 / 2 : ℚ) ^ n

/-- Weight of one regular site. -/
def weight (n : ℕ) : ℚ := tailWeight (n + 1)

/-- Weighted average of a sequence whose constant tail begins at `N`. -/
def mass : ℕ → (ℕ → ℚ) → ℚ → ℚ
  | 0, _, tail => tail
  | N + 1, f, tail => (f 0 + mass N (fun n => f (n+1)) tail) / 2

/-- The tail term accounts for all indices from the cutoff onwards. -/
theorem mass_eq_sum (N : ℕ) (f : ℕ → ℚ) (tail : ℚ) :
    mass N f tail = (∑ i ∈ Finset.range N, weight i * f i) + tailWeight N * tail := by
  induction N generalizing f with
  | zero => simp [mass, tailWeight]
  | succ N ih =>
    rw [mass, ih, Finset.sum_range_succ']
    have hs : (∑ i ∈ Finset.range N, weight (i + 1) * f (i + 1)) =
        (∑ i ∈ Finset.range N, weight i * f (i + 1)) / 2 := by
      simp_rw [weight, tailWeight, pow_succ (1 / 2 : ℚ) (_ + 1), mul_right_comm _ (1 / 2 : ℚ)]
      rw [← Finset.sum_mul]
      ring
    rw [hs]
    simp [weight, tailWeight, pow_succ]
    ring

/-- Moving the cutoff past another copy of the constant tail preserves the sum. -/
theorem mass_succ_of_eq_tail (N : ℕ) (f : ℕ → ℚ) (tail : ℚ) (h : f N = tail) :
    mass (N + 1) f tail = mass N f tail := by
  rw [mass_eq_sum, mass_eq_sum, Finset.sum_range_succ, h]
  simp only [weight, tailWeight, pow_succ]
  ring

theorem mass_eq_of_stable {N M : ℕ} (f : ℕ → ℚ) (tail : ℚ)
    (hNM : N ≤ M) (hs : ∀ i ≥ N, f i = tail) : mass M f tail = mass N f tail := by
  induction M, hNM using Nat.le_induction with
  | base => rfl
  | succ M h ih => rw [mass_succ_of_eq_tail M f tail (hs M h), ih]

theorem mass_le_const (N : ℕ) (f : ℕ → ℚ) (tail c : ℚ)
    (hf : ∀ n, f n ≤ c) (ht : tail ≤ c) : mass N f tail ≤ c := by
  induction N generalizing f with
  | zero => exact ht
  | succ N ih =>
    simp only [mass]
    have := ih (fun n => f (n+1)) (fun n => hf (n+1))
    linarith [hf 0]

/-- Effective regular values in two channels. Each plus sequence stabilizes at
the height of the zero centre and each minus sequence at the height of the one
centre. -/
structure Profile where
  height : Bool → ℕ
  plus : Bool → ℕ → ℕ
  minus : Bool → ℕ → ℕ
  cutoff : ℕ
  plus_stable : ∀ k n, cutoff ≤ n → plus k n = height false
  minus_stable : ∀ k n, cutoff ≤ n → minus k n = height true

namespace Profile

def difference (p : Profile) (k : Bool) (n : ℕ) : ℚ :=
  (p.plus k n : ℚ) - p.minus k n

def tailDifference (p : Profile) : ℚ := (p.height false : ℚ) - p.height true

def signedMass (p : Profile) (k : Bool) : ℚ :=
  mass p.cutoff (p.difference k) p.tailDifference

/-- Principal-profile equations when all supplementary coordinates vanish. -/
def MassEquations (p : Profile) : Prop := ∀ k, p.signedMass k = (p.height k : ℚ)

/-- Coordinatewise comparison on the two centres and all four sequences. -/
def Below (p q : Profile) : Prop :=
  (∀ k, p.height k ≤ q.height k) ∧
  (∀ k n, p.plus k n ≤ q.plus k n) ∧ (∀ k n, p.minus k n ≤ q.minus k n)

theorem signedMass_eq_of_le (p : Profile) (k : Bool) {N : ℕ} (hN : p.cutoff ≤ N) :
    p.signedMass k = mass N (p.difference k) p.tailDifference := by
  apply (mass_eq_of_stable _ _ hN ?_).symm
  intro i hi
  simp [difference, tailDifference, p.plus_stable k i hi, p.minus_stable k i hi]

end Profile

/-- On each channel the first witness has early plus values `2,0`, and
the second witness has `0,4`. Both have equal plus and minus tails. -/
def witness (second : Bool) : Profile where
  height _ := 1
  plus _ n := if n = 0 then (if second then 0 else 2)
    else if n = 1 then (if second then 4 else 0) else 1
  minus _ n := if n < 2 then 0 else 1
  cutoff := 2
  plus_stable _ n hn := by simp [show n ≠ 0 by omega, show n ≠ 1 by omega]
  minus_stable _ n hn := by simp [Nat.not_lt.mpr hn]

theorem witness_massEquations (second : Bool) : (witness second).MassEquations := by
  intro k
  cases second <;> norm_num [witness, Profile.signedMass, Profile.difference,
    Profile.tailDifference, mass]

/-- Each channel has zero early common plus entries and total remaining positive
mass at most `1/4`. This bound precedes use of the principal-profile equations. -/
theorem signedMass_le_quarter (p : Profile) (hx : p.Below (witness false))
    (hy : p.Below (witness true)) (k : Bool) : p.signedMass k ≤ 1 / 4 := by
  have h0 : p.plus k 0 = 0 := Nat.le_zero.mp (hy.2.1 k 0)
  have h1 : p.plus k 1 = 0 := Nat.le_zero.mp (hx.2.1 k 1)
  have hd0 : p.difference k 0 ≤ 0 := by simp [Profile.difference, h0]
  have hd1 : p.difference k 1 ≤ 0 := by simp [Profile.difference, h1]
  have ht : p.tailDifference ≤ 1 := by
    have ha : p.height false ≤ 1 := hx.1 false
    have hb : (p.height false : ℚ) ≤ 1 := by exact_mod_cast ha
    unfold Profile.tailDifference
    linarith [Nat.cast_nonneg (α := ℚ) (p.height true)]
  have hlate (n : ℕ) : p.difference k (n + 2) ≤ 1 := by
    have h := hx.2.1 k (n + 2)
    have ha : p.plus k (n + 2) ≤ 1 := by simpa [witness] using h
    have hb : (p.plus k (n + 2) : ℚ) ≤ 1 := by exact_mod_cast ha
    unfold Profile.difference
    linarith [Nat.cast_nonneg (α := ℚ) (p.minus k (n+2))]
  rw [p.signedMass_eq_of_le k (show p.cutoff ≤ p.cutoff + 2 by omega)]
  simp only [mass]
  linarith [mass_le_const p.cutoff (fun n => p.difference k (n+2)) p.tailDifference 1 hlate ht]

/-- Realizable common divisors with zero supplementary coordinates have zero
heights. Consequently all four of their regular sequences have finite support. -/
theorem common_profile_heights_zero (p : Profile) (hp : p.MassEquations)
    (hx : p.Below (witness false)) (hy : p.Below (witness true)) (k : Bool) :
    p.height k = 0 := by
  have h := signedMass_le_quarter p hx hy k
  rw [hp k] at h
  have hlt : (p.height k : ℚ) < 1 := by linarith
  have hn : p.height k < 1 := by exact_mod_cast hlt
  omega

theorem common_profile_eventually_zero (p : Profile) (hp : p.MassEquations)
    (hx : p.Below (witness false)) (hy : p.Below (witness true))
    (k : Bool) {n : ℕ} (hn : p.cutoff ≤ n) : p.plus k n = 0 ∧ p.minus k n = 0 := by
  simp [p.plus_stable k n hn, p.minus_stable k n hn, common_profile_heights_zero p hp hx hy]

/-- The balanced column contributes one at the plus and minus sites of
the same channel and index. -/
def balancedEntry (channel : Bool) (index : ℕ) (k : Bool) (n : ℕ) : ℕ :=
  if k = channel ∧ n = index then 1 else 0

/-- Adjoin the balanced column at one index, leaving the heights fixed. -/
def Profile.addBalanced (p : Profile) (channel : Bool) (index : ℕ) : Profile where
  height := p.height
  plus k n := p.plus k n + balancedEntry channel index k n
  minus k n := p.minus k n + balancedEntry channel index k n
  cutoff := max p.cutoff (index + 1)
  plus_stable k n hn := by
    have hs := p.plus_stable k n ((le_max_left ..).trans hn)
    have hi : n ≠ index := by omega
    simp [balancedEntry, hi, hs]
  minus_stable k n hn := by
    have hs := p.minus_stable k n ((le_max_left ..).trans hn)
    have hi : n ≠ index := by omega
    simp [balancedEntry, hi, hs]

theorem Profile.signedMass_addBalanced (p : Profile) (channel : Bool) (index : ℕ) (k : Bool) :
    (p.addBalanced channel index).signedMass k = p.signedMass k := by
  have hd : (p.addBalanced channel index).difference k = p.difference k := by
    funext n
    simp [Profile.difference, Profile.addBalanced]
  rw [p.signedMass_eq_of_le k (le_max_left p.cutoff (index + 1))]
  unfold Profile.signedMass
  rw [hd]
  rfl

theorem Profile.addBalanced_massEquations (p : Profile) (hp : p.MassEquations)
    (channel : Bool) (index : ℕ) : (p.addBalanced channel index).MassEquations := by
  intro k
  rw [p.signedMass_addBalanced]
  exact hp k

/-- Every common profile satisfying the mass equations can be strictly
enlarged by a balanced column and still lies below both witness profiles. -/
theorem common_profile_balanced_extension (p : Profile) (hp : p.MassEquations)
    (hx : p.Below (witness false)) (hy : p.Below (witness true)) :
    ∃ n ≥ 2, (p.addBalanced false n).Below (witness false) ∧
      (p.addBalanced false n).Below (witness true) ∧ ¬ (p.addBalanced false n).Below p := by
  let n := max p.cutoff 2
  have hc : p.cutoff ≤ n := le_max_left ..
  have ht : 2 ≤ n := le_max_right ..
  have hz := common_profile_eventually_zero p hp hx hy false hc
  have hb (second : Bool) (h : p.Below (witness second)) :
      (p.addBalanced false n).Below (witness second) := by
    refine ⟨h.1, ?_, ?_⟩
    · intro k m
      by_cases he : k = false ∧ m = n
      · obtain ⟨rfl, rfl⟩ := he
        simp [Profile.addBalanced, balancedEntry, hz.1, witness,
          show n ≠ 0 by omega, show n ≠ 1 by omega]
      · simpa [Profile.addBalanced, balancedEntry, he] using h.2.1 k m
    · intro k m
      by_cases he : k = false ∧ m = n
      · obtain ⟨rfl, rfl⟩ := he
        simp [Profile.addBalanced, balancedEntry, hz.2, witness, Nat.not_lt.mpr ht]
      · simpa [Profile.addBalanced, balancedEntry, he] using h.2.2 k m
  refine ⟨n, ht, hb false hx, hb true hy, ?_⟩
  intro h
  have he := h.2.1 false n
  simp [Profile.addBalanced, balancedEntry] at he

end UnconditionalCounterexample.DyadicProfiles
