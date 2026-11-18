import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.Order.Ring.Abs
import Lean.Elab.Tactic.Omega

/-!
# Bounded normalized words and construction stages

The primary profile of a pure normalized word determines its signed b- and
q-exponents. A uniform bound on an effective profile bounds both exponent sequences.
Vanishing on initial primaries forces vanishing on initial construction stages, and
the latest exponent of a nonempty effective word is positive.

All profile representation formulas are explicit hypotheses. This module does
not assert that an actual rational function has such a representation; that
algebraic construction belongs to the realization step.
-/

namespace UnconditionalCounterexample.NormalizedWords

/-- The primary profile of a signed word in normalized b and q generators. -/
structure Represents (s u g : ℕ → ℤ) : Prop where
  initial : g 0 = 3 * s 0 + 2 * u 0
  odd : ∀ n, g (2 * n + 1) = u n
  even_succ : ∀ n, g (2 * n + 2) = 3 * s (n + 1) + 2 * u (n + 1) + 2 * u n

/-- Effective bounded primary values bound every signed exponent uniformly. -/
theorem exponent_bounds {s u g : ℕ → ℤ} (h : Represents s u g) {r : ℤ}
    (hbound : ∀ j, 0 ≤ g j ∧ g j ≤ r) :
    ∀ n, |s n| ≤ 2 * r ∧ 0 ≤ u n ∧ u n ≤ r := by
  have hu (n : ℕ) : 0 ≤ u n ∧ u n ≤ r := by
    rw [← h.odd n]
    exact hbound _
  intro n
  refine ⟨abs_le.mpr ?_, hu n⟩
  cases n with
  | zero =>
    have hg := hbound 0
    have hu0 := hu 0
    rw [h.initial] at hg
    omega
  | succ n =>
    have hg := hbound (2 * n + 2)
    have hun := hu n
    have hun1 := hu (n + 1)
    rw [h.even_succ] at hg
    omega

/-- A zero primary prefix forces both exponent sequences to vanish there. -/
theorem exponents_zero_of_profile_prefix {s u g : ℕ → ℤ}
    (h : Represents s u g) (N : ℕ)
    (hzero : ∀ j, j < 2 * N + 2 → g j = 0) :
    ∀ n, n ≤ N → s n = 0 ∧ u n = 0 := by
  have hu (n : ℕ) (hn : n ≤ N) : u n = 0 := by
    rw [← h.odd n]
    exact hzero _ (by omega)
  intro n hn
  refine ⟨?_, hu n hn⟩
  cases n with
  | zero =>
    have hg := hzero 0 (by omega)
    rw [h.initial, hu 0 (by omega)] at hg
    omega
  | succ n =>
    have hg := hzero (2 * n + 2) (by omega)
    rw [h.even_succ, hu (n + 1) hn, hu n (by omega)] at hg
    omega

inductive Generator
  | b (n : ℕ)
  | q (n : ℕ)
  deriving DecidableEq

/-- Construction order b0, b1, q0, b2, q1, ... . -/
def Generator.stage : Generator → ℕ
  | .b 0 => 0
  | .b (n + 1) => 2 * n + 1
  | .q n => 2 * n + 2

def Generator.exponent (s u : ℕ → ℤ) : Generator → ℤ
  | .b n => s n
  | .q n => u n

/-- A nonzero coefficient with no later nonzero coefficient is positive. -/
theorem exponent_pos_of_latest {s u g : ℕ → ℤ} (h : Represents s u g)
    (hnonneg : ∀ j, 0 ≤ g j) (i : Generator)
    (hi : i.exponent s u ≠ 0)
    (hlate : ∀ j : Generator, i.stage < j.stage → j.exponent s u = 0) :
    0 < i.exponent s u := by
  cases i with
  | q n =>
    change 0 < u n
    have hu : 0 ≤ u n := by rw [← h.odd n]; exact hnonneg _
    change u n ≠ 0 at hi
    omega
  | b n =>
    cases n with
    | zero =>
      have hu : u 0 = 0 := hlate (.q 0) (by decide)
      have hg := hnonneg 0
      rw [h.initial, hu] at hg
      change s 0 ≠ 0 at hi
      change 0 < s 0
      omega
    | succ n =>
      have hu : u n = 0 := hlate (.q n) (by dsimp [Generator.stage]; omega)
      have hu1 : u (n + 1) = 0 := hlate (.q (n + 1)) (by dsimp [Generator.stage]; omega)
      have hg := hnonneg (2 * n + 2)
      rw [h.even_succ, hu, hu1] at hg
      change s (n + 1) ≠ 0 at hi
      change 0 < s (n + 1)
      omega

/-- The finite set of normalized generators with nonzero exponent. -/
def wordSupport (s u : ℕ →₀ ℤ) : Finset Generator :=
  s.support.image Generator.b ∪ u.support.image Generator.q

@[simp] theorem mem_wordSupport (s u : ℕ →₀ ℤ) (i : Generator) :
    i ∈ wordSupport s u ↔ i.exponent s u ≠ 0 := by
  cases i <;> simp [wordSupport, Generator.exponent]

/-- Every nonempty effective finite word has a positive latest coefficient. -/
theorem exists_latest_positive {s u : ℕ →₀ ℤ} {g : ℕ → ℤ}
    (h : Represents s u g) (hnonneg : ∀ j, 0 ≤ g j)
    (hword : ∃ i : Generator, i.exponent s u ≠ 0) :
    ∃ i : Generator, 0 < i.exponent s u ∧
      ∀ j : Generator, i.stage < j.stage → j.exponent s u = 0 := by
  have hsupport : (wordSupport s u).Nonempty := by
    obtain ⟨i, hi⟩ := hword
    exact ⟨i, (mem_wordSupport s u i).mpr hi⟩
  obtain ⟨i, hi, himax⟩ := Finset.exists_max_image (wordSupport s u) Generator.stage hsupport
  have hlate : ∀ j : Generator, i.stage < j.stage → j.exponent s u = 0 := by
    intro j hj
    by_contra hne
    have hji := himax j ((mem_wordSupport s u j).mpr hne)
    omega
  exact ⟨i, exponent_pos_of_latest h hnonneg i ((mem_wordSupport s u i).mp hi) hlate, hlate⟩

/-- Primary-prefix escape implies escape from every bounded raw-stage prefix. -/
theorem stage_exponents_zero_of_profile_prefix {s u g : ℕ → ℤ}
    (h : Represents s u g) (N : ℕ)
    (hzero : ∀ j, j < 2 * N + 2 → g j = 0) :
    ∀ i : Generator, i.stage ≤ N → i.exponent s u = 0 := by
  intro i hi
  have hprefix := exponents_zero_of_profile_prefix h N hzero
  cases i with
  | q n =>
    exact (hprefix n (by dsimp [Generator.stage] at hi; omega)).2
  | b n =>
    cases n with
    | zero => exact (hprefix 0 (by omega)).1
    | succ n => exact (hprefix (n + 1) (by dsimp [Generator.stage] at hi; omega)).1

/-- A nonzero represented profile cannot have an empty normalized word. -/
theorem exists_nonzero_exponent {s u g : ℕ → ℤ} (h : Represents s u g)
    (hprofile : ∃ j, g j ≠ 0) :
    ∃ i : Generator, i.exponent s u ≠ 0 := by
  by_contra hnone
  have hs (n : ℕ) : s n = 0 := by
    by_contra hn
    exact hnone ⟨.b n, hn⟩
  have hu (n : ℕ) : u n = 0 := by
    by_contra hn
    exact hnone ⟨.q n, hn⟩
  obtain ⟨j, hj⟩ := hprofile
  apply hj
  obtain ⟨n, hn | hn⟩ : ∃ n : ℕ, j = 2 * n ∨ j = 2 * n + 1 := by
    exact ⟨j / 2, by omega⟩
  · cases n with
    | zero =>
      rw [hn]
      simpa [hs, hu] using h.initial
    | succ n =>
      have heq : j = 2 * n + 2 := by omega
      rw [heq, h.even_succ, hs, hu, hu]
      omega
  · rw [hn, h.odd, hu]

/-- Uniform signed bounds expressed in the construction's single generator index. -/
theorem generator_exponent_bound {s u g : ℕ → ℤ} (h : Represents s u g) {r : ℤ}
    (hbound : ∀ j, 0 ≤ g j ∧ g j ≤ r) :
    ∀ i : Generator, |i.exponent s u| ≤ 2 * r := by
  have hb := exponent_bounds h hbound
  have hr : 0 ≤ r := (hbound 0).1.trans (hbound 0).2
  intro i
  cases i with
  | b n => exact (hb n).1
  | q n =>
    change |u n| ≤ 2 * r
    rw [abs_of_nonneg (hb n).2.1]
    have hn := (hb n).2.2
    omega

/-- The finite-stage scheduling interface: a nonzero bounded effective profile
vanishing on a long primary prefix yields a bounded word whose latest exponent
is positive and occurs beyond any prescribed construction-stage prefix. -/
theorem exists_bounded_latest_beyond {s u : ℕ →₀ ℤ} {g : ℕ → ℤ}
    (h : Represents s u g) {r : ℤ} (hbound : ∀ j, 0 ≤ g j ∧ g j ≤ r)
    (hprofile : ∃ j, g j ≠ 0) (N : ℕ)
    (hzero : ∀ j, j < 2 * N + 2 → g j = 0) :
    ∃ i : Generator, N < i.stage ∧ 0 < i.exponent s u ∧
      i.exponent s u ≤ 2 * r ∧
      (∀ j : Generator, |j.exponent s u| ≤ 2 * r) ∧
      ∀ j : Generator, i.stage < j.stage → j.exponent s u = 0 := by
  obtain ⟨i, hipos, hilate⟩ := exists_latest_positive h (fun j => (hbound j).1)
    (exists_nonzero_exponent h hprofile)
  have hiN : N < i.stage := by
    by_contra hle
    have hz := stage_exponents_zero_of_profile_prefix h N hzero i (by omega)
    omega
  have hb := generator_exponent_bound h hbound
  have hib : i.exponent s u ≤ 2 * r := (le_abs_self _).trans (hb i)
  exact ⟨i, hiN, hipos, hib, hb, hilate⟩

end UnconditionalCounterexample.NormalizedWords
