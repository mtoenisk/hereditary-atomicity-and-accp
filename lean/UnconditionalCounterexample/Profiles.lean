import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Tactic.SplitIfs
import Lean.Elab.Tactic.Omega

/-!
# Primary profiles

The primary coordinates are integer valued, and the horizontal value records their
eventual value. The profile primaryAtomProfile n is zero before 2*n, two at 2*n, and
one afterwards.
-/

namespace UnconditionalCounterexample

/-- An integer sequence has the specified eventual value. -/
def EventuallyConstantProfile (g : ℕ → ℤ) (r : ℤ) : Prop :=
  ∃ N : ℕ, ∀ i : ℕ, N ≤ i → g i = r

/-- The primary profile of the order-one element aₙ. -/
def primaryAtomProfile (n i : ℕ) : ℤ :=
  if i < 2 * n then 0 else if i = 2 * n then 2 else 1

@[simp]
theorem primaryAtomProfile_of_lt {n i : ℕ} (hi : i < 2 * n) :
    primaryAtomProfile n i = 0 := by
  simp [primaryAtomProfile, hi]

@[simp]
theorem primaryAtomProfile_pivot (n : ℕ) : primaryAtomProfile n (2 * n) = 2 := by
  simp [primaryAtomProfile]

@[simp]
theorem primaryAtomProfile_of_gt {n i : ℕ} (hi : 2 * n < i) :
    primaryAtomProfile n i = 1 := by
  simp [primaryAtomProfile, show ¬i < 2 * n by omega, show i ≠ 2 * n by omega]

theorem primaryAtomProfile_nonneg (n i : ℕ) : 0 ≤ primaryAtomProfile n i := by
  unfold primaryAtomProfile
  split_ifs <;> omega

theorem primaryAtomProfile_eventually_one (n : ℕ) :
    EventuallyConstantProfile (primaryAtomProfile n) 1 := by
  refine ⟨2 * n + 1, fun i hi => primaryAtomProfile_of_gt ?_⟩
  omega

/-- Every finitely supported primary profile has eventual value zero. -/
theorem finsupp_eventually_zero (g : ℕ →₀ ℤ) :
    EventuallyConstantProfile g 0 := by
  classical
  refine ⟨g.support.sup id + 1, ?_⟩
  intro i hi
  apply Finsupp.notMem_support_iff.mp
  intro hmem
  have hle : i ≤ g.support.sup id := Finset.le_sup (f := id) hmem
  omega

end UnconditionalCounterexample
