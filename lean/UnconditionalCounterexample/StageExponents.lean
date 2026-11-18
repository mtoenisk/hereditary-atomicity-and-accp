import Mathlib.Algebra.Ring.Subring.Basic
import UnconditionalCounterexample.NormalizedWords
import UnconditionalCounterexample.RawWords
import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# Actual finite exponents and the construction's stage lists

The bijection between b/q generators and zero-based raw stages transports an
actual finite principal exponent vector to the profile formulas. A bounded,
effective, nonempty profile beyond a prefix gives a positive latest exponent
in the exact stage list with budget n+1. The Finsupp product is proved equal to
that listed word. Finally actual signed subring representations beyond each
prefix produce a single actual word sequence whose stages tend to infinity.

The representation/profile hypotheses in the last theorem are explicit; their
algebraic and valuation producers are separate modules.
-/

namespace UnconditionalCounterexample.StageExponents

open NormalizedWords Filter

/-- The paper's interleaving is a bijective indexing of all normalized generators. -/
theorem stage_injective : Function.Injective Generator.stage := by
  intro i j hij
  cases i with
  | b n =>
    cases j with
    | b m =>
      cases n <;> cases m <;> simp_all [Generator.stage]
    | q m =>
      cases n <;> simp only [Generator.stage] at hij <;> omega
  | q n =>
    cases j with
    | b m =>
      cases m <;> simp only [Generator.stage] at hij <;> omega
    | q m =>
      simp only [Generator.stage] at hij
      congr
      omega

theorem stage_surjective : Function.Surjective Generator.stage := by
  intro n
  by_cases hn : n = 0
  · exact ⟨.b 0, hn.symm⟩
  · by_cases hodd : n % 2 = 1
    · refine ⟨.b (n / 2 + 1), ?_⟩
      simp only [Generator.stage]
      omega
    · refine ⟨.q (n / 2 - 1), ?_⟩
      simp only [Generator.stage]
      omega

noncomputable def bExponents (e : ℕ →₀ ℤ) : ℕ →₀ ℤ :=
  e.comapDomain (fun n => (Generator.b n).stage)
    (fun _ _ _ _ h => Generator.b.inj (stage_injective h))

noncomputable def qExponents (e : ℕ →₀ ℤ) : ℕ →₀ ℤ :=
  e.comapDomain (fun n => (Generator.q n).stage)
    (fun _ _ _ _ h => Generator.q.inj (stage_injective h))

@[simp] theorem generator_exponent (e : ℕ →₀ ℤ) (i : Generator) :
    i.exponent (bExponents e) (qExponents e) = e i.stage := by
  cases i <;> rfl

/-- The finite principal representation in one raw-stage index has exactly the
latest-stage bound already proved for the interleaved b/q primary profiles. -/
theorem exists_bounded_latest_beyond (e : ℕ →₀ ℤ) (g : ℕ → ℤ)
    (h : Represents (bExponents e) (qExponents e) g)
    {r : ℤ} (hbound : ∀ j, 0 ≤ g j ∧ g j ≤ r) (hprofile : ∃ j, g j ≠ 0)
    (N : ℕ) (hzero : ∀ j, j < 2 * N + 2 → g j = 0) :
    ∃ n : ℕ, N < n ∧ 0 < e n ∧ e n ≤ 2 * r ∧
      (∀ j, |e j| ≤ 2 * r) ∧ ∀ j, n < j → e j = 0 := by
  obtain ⟨i, hiN, hip, hib, hb, hlate⟩ :=
    NormalizedWords.exists_bounded_latest_beyond h hbound hprofile N hzero
  refine ⟨i.stage, hiN, ?_, ?_, ?_, ?_⟩
  · simpa using hip
  · simpa using hib
  · intro j
    obtain ⟨a, rfl⟩ := stage_surjective j
    simpa using hb a
  · intro j hj
    obtain ⟨a, rfl⟩ := stage_surjective j
    simpa using hlate a hj

/-- A positive latest exponent with a uniform bound occurs in the exact list
at that construction stage, whose paper budget is n+1. -/
theorem exists_stageWord_of_latest (e : ℕ →₀ ℤ) (n r : ℕ)
    (hpos : 0 < e n) (hbound : ∀ j, |e j| ≤ r) (hr : r ≤ n + 1) :
    ∃ w : RawWords.StageWord n (n + 1),
      (∀ j < n, w.oldExponent j = e j) ∧ (w.latestExponent : ℤ) = e n := by
  have hbox : ∀ j < n, -((n + 1 : ℕ) : ℤ) ≤ e j ∧ e j ≤ n + 1 := by
    intro j _
    have hj := abs_le.mp (hbound j)
    constructor <;> omega
  have ha : 0 < (e n).toNat ∧ (e n).toNat ≤ n + 1 := by
    have hn := abs_le.mp (hbound n)
    omega
  obtain ⟨w, hw, hwa⟩ := RawWords.stageWord_covers e hbox (e n).toNat ha
  exact ⟨w, hw, by rw [hwa, Int.toNat_of_nonneg (le_of_lt hpos)]⟩

/-- The finite principal-product representation is literally the listed word;
no values beyond its latest nonzero stage are included. -/
theorem prod_eq_listed_word {L : Type*} [Field L] (W : ℕ → L)
    (e : ℕ →₀ ℤ) (n r : ℕ) (w : RawWords.StageWord n r)
    (hold : ∀ j < n, w.oldExponent j = e j)
    (hlatest : (w.latestExponent : ℤ) = e n)
    (hzero : ∀ j, n < j → e j = 0) :
    e.prod (fun j z => W j ^ z) = W n ^ w.latestExponent *
      ∏ j ∈ Finset.range n, W j ^ w.oldExponent j := by
  have hs : e.support ⊆ Finset.range (n + 1) := by
    intro j hj
    apply Finset.mem_range.mpr
    by_contra hle
    exact Finsupp.mem_support_iff.mp hj (hzero j (by omega))
  rw [Finsupp.prod_of_support_subset e hs _ (by intros; simp), Finset.prod_range_succ]
  have hprefix : (∏ j ∈ Finset.range n, W j ^ e j) =
      ∏ j ∈ Finset.range n, W j ^ w.oldExponent j := by
    apply Finset.prod_congr rfl
    intro j hj
    rw [hold j (Finset.mem_range.mp hj)]
  rw [hprefix, ← hlatest, zpow_natCast, mul_comm]

/-- Profile escape yields an actual finite-stage word with a positive latest
exponent, at an arbitrarily late stage past the fixed exponent budget. -/
theorem exists_listed_word_beyond (e : ℕ →₀ ℤ) (g : ℕ → ℤ)
    (h : Represents (bExponents e) (qExponents e) g)
    (r N : ℕ) (hbound : ∀ j, 0 ≤ g j ∧ g j ≤ r) (hprofile : ∃ j, g j ≠ 0)
    (hzero : ∀ j, j < 2 * max N (2 * r) + 2 → g j = 0) :
    ∃ n : ℕ, N < n ∧ ∃ w : RawWords.StageWord n (n + 1),
      (∀ j < n, w.oldExponent j = e j) ∧ (w.latestExponent : ℤ) = e n ∧
      ∀ j, n < j → e j = 0 := by
  obtain ⟨n, hn, hp, _, hb, hz⟩ := exists_bounded_latest_beyond e g h hbound hprofile
    (max N (2 * r)) hzero
  have hb' : ∀ j, |e j| ≤ (2 * r : ℕ) := by simpa only [Nat.cast_mul, Nat.cast_ofNat] using hb
  obtain ⟨w, hw, hwa⟩ := exists_stageWord_of_latest e n (2 * r) hp hb' (by omega)
  exact ⟨n, by omega, w, hw, hwa, hz⟩

/-- Choose actual subring elements with latest raw stages tending to infinity.
The only representation input is a signed finite principal product with the
explicit bounded effective primary profile, available beyond each prefix. -/
theorem exists_escaping_listed_sequence {R L : Type*} [CommRing R] [Field L]
    (f : R →+* L) (T : Subring R) (W : ℕ → L) (r : ℕ)
    (hextract : ∀ N : ℕ, ∃ y : T, ∃ e : ℕ →₀ ℤ, ∃ g : ℕ → ℤ,
      (f (y : R) = e.prod (fun j z => W j ^ z) ∨
        f (y : R) = -(e.prod (fun j z => W j ^ z))) ∧
      Represents (bExponents e) (qExponents e) g ∧
      (∀ j, 0 ≤ g j ∧ g j ≤ r) ∧ (∃ j, g j ≠ 0) ∧
      ∀ j, j < 2 * N + 2 → g j = 0) :
    ∃ y : ℕ → T, ∃ stage : ℕ → ℕ, ∃ w : ∀ i, RawWords.StageWord (stage i) (stage i + 1),
      (∀ i, i < stage i) ∧ Tendsto stage atTop atTop ∧
      ∀ i, f (y i : R) = W (stage i) ^ (w i).latestExponent *
        ∏ j ∈ Finset.range (stage i), W j ^ (w i).oldExponent j := by
  classical
  have hchoose (i : ℕ) : ∃ y : T, ∃ n : ℕ, ∃ w : RawWords.StageWord n (n + 1),
      i < n ∧ f (y : R) = W n ^ w.latestExponent *
        ∏ j ∈ Finset.range n, W j ^ w.oldExponent j := by
    obtain ⟨y, e, g, hy, hrep, hb, hg, hz⟩ := hextract (max i (2 * r))
    obtain ⟨n, hn, w, hw, hwa, hlate⟩ := exists_listed_word_beyond e g hrep r i hb hg hz
    have hp := prod_eq_listed_word W e n (n + 1) w hw hwa hlate
    cases hy with
    | inl hy => exact ⟨y, n, w, hn, hy.trans hp⟩
    | inr hy =>
      refine ⟨-y, n, w, hn, ?_⟩
      change f (-(y : R)) = _
      rw [map_neg, hy, neg_neg]
      exact hp
  choose y stage w hstage hword using hchoose
  refine ⟨y, stage, w, hstage, ?_, hword⟩
  apply tendsto_atTop_atTop.mpr
  intro N
  exact ⟨N, fun i hi => hi.trans (hstage i).le⟩

end UnconditionalCounterexample.StageExponents



namespace UnconditionalCounterexample.StageExponents

open NormalizedWords Filter

/-- Preserve the fixed exponent budget when passing to the stage's larger list. -/
theorem exists_bounded_listed_word_beyond (e : ℕ →₀ ℤ) (g : ℕ → ℤ)
    (h : Represents (bExponents e) (qExponents e) g)
    (r N : ℕ) (hbound : ∀ j, 0 ≤ g j ∧ g j ≤ r) (hprofile : ∃ j, g j ≠ 0)
    (hzero : ∀ j, j < 2 * max N (2 * r) + 2 → g j = 0) :
    ∃ n : ℕ, N < n ∧ ∃ w : RawWords.StageWord n (n + 1),
      (∀ j < n, w.oldExponent j = e j) ∧ (w.latestExponent : ℤ) = e n ∧
      (∀ j, n < j → e j = 0) ∧ w.latestExponent ≤ 2 * r ∧
      ∀ j, |w.oldExponent j| ≤ (2 * r : ℕ) := by
  obtain ⟨n, hn, w, hw, hwa, hlate⟩ := exists_listed_word_beyond e g h r N hbound hprofile hzero
  have hb : ∀ j, |e j| ≤ (2 * r : ℕ) := by
    intro j
    obtain ⟨i, rfl⟩ := stage_surjective j
    simpa only [generator_exponent, Nat.cast_mul, Nat.cast_ofNat] using
      NormalizedWords.generator_exponent_bound h hbound i
  refine ⟨n, hn, w, hw, hwa, hlate, ?_, ?_⟩
  · have he := abs_le.mp (hb n)
    omega
  · intro j
    by_cases hj : j < n
    · rw [hw j hj]
      exact hb j
    · simp only [RawWords.StageWord.oldExponent, dite_eq_right hj, abs_zero]
      positivity

/-- A single actual subring sequence retains the uniform latest and predecessor
exponent bounds needed for the local conductor step, independently of stage. -/
theorem exists_bounded_escaping_listed_sequence {R L : Type*} [CommRing R] [Field L]
    (f : R →+* L) (T : Subring R) (W : ℕ → L) (r : ℕ)
    (hextract : ∀ N : ℕ, ∃ y : T, ∃ e : ℕ →₀ ℤ, ∃ g : ℕ → ℤ,
      (f (y : R) = e.prod (fun j z => W j ^ z) ∨
        f (y : R) = -(e.prod (fun j z => W j ^ z))) ∧
      Represents (bExponents e) (qExponents e) g ∧
      (∀ j, 0 ≤ g j ∧ g j ≤ r) ∧ (∃ j, g j ≠ 0) ∧
      ∀ j, j < 2 * N + 2 → g j = 0) :
    ∃ y : ℕ → T, ∃ stage : ℕ → ℕ, ∃ w : ∀ i, RawWords.StageWord (stage i) (stage i + 1),
      (∀ i, i < stage i) ∧ Tendsto stage atTop atTop ∧
      (∀ i, (w i).latestExponent ≤ 2 * r) ∧
      (∀ i j, |(w i).oldExponent j| ≤ (2 * r : ℕ)) ∧
      ∀ i, f (y i : R) = W (stage i) ^ (w i).latestExponent *
        ∏ j ∈ Finset.range (stage i), W j ^ (w i).oldExponent j := by
  classical
  have hchoose (i : ℕ) : ∃ y : T, ∃ n : ℕ, ∃ w : RawWords.StageWord n (n + 1),
      i < n ∧ w.latestExponent ≤ 2 * r ∧ (∀ j, |w.oldExponent j| ≤ (2 * r : ℕ)) ∧
      f (y : R) = W n ^ w.latestExponent *
        ∏ j ∈ Finset.range n, W j ^ w.oldExponent j := by
    obtain ⟨y, e, g, hy, hrep, hb, hg, hz⟩ := hextract (max i (2 * r))
    obtain ⟨n, hn, w, hw, hwa, hlate, hlatest, hold⟩ :=
      exists_bounded_listed_word_beyond e g hrep r i hb hg hz
    have hp := prod_eq_listed_word W e n (n + 1) w hw hwa hlate
    cases hy with
    | inl hy => exact ⟨y, n, w, hn, hlatest, hold, hy.trans hp⟩
    | inr hy =>
      refine ⟨-y, n, w, hn, hlatest, hold, ?_⟩
      change f (-(y : R)) = _
      rw [map_neg, hy, neg_neg]
      exact hp
  choose y stage w hstage hlatest hold hword using hchoose
  refine ⟨y, stage, w, hstage, ?_, hlatest, hold, hword⟩
  apply tendsto_atTop_atTop.mpr
  intro N
  exact ⟨N, fun i hi => hi.trans (hstage i).le⟩

end UnconditionalCounterexample.StageExponents
