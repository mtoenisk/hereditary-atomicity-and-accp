import UnconditionalCounterexample.StageExponents
import UnconditionalCounterexample.Variations.DyadicColumns

/-!
# Bounded words for the dyadic construction

An effective regular profile bounded by `h` bounds all exponents of its unique
balanced and adjacent columns by `h`. The partial order on the introduction of
columns forces the latest exponent to be positive, including when it belongs
to a signed adjacent column. Stages assigned to auxiliary columns may occur
anywhere between the regular ones.
-/

noncomputable section

namespace UnconditionalCounterexample.DyadicEscape

/-- The two kinds of regular columns in each of the two channels. -/
inductive Generator
  | balanced (k : Bool) (n : ℕ)
  | adjacent (k : Bool) (n : ℕ)
  deriving DecidableEq

/-- The precedence requirements on the regular part of the simultaneous schedule. -/
structure Schedule where
  stage : Generator → ℕ
  injective : Function.Injective stage
  adjacent_succ : ∀ k n, stage (.adjacent k n) < stage (.adjacent k (n+1))
  balanced_succ : ∀ k n, stage (.adjacent k n) < stage (.balanced k (n+1))

theorem Schedule.index_le_adjacent (s : Schedule) (k : Bool) (n : ℕ) :
    n ≤ s.stage (.adjacent k n) := by
  induction n with
  | zero => exact Nat.zero_le _
  | succ n ih => exact Nat.succ_le_of_lt (ih.trans_lt (s.adjacent_succ k n))

theorem Schedule.index_le_balanced (s : Schedule) (k : Bool) (n : ℕ) :
    n ≤ s.stage (.balanced k n) := by
  cases n with
  | zero => exact Nat.zero_le _
  | succ n => exact Nat.succ_le_of_lt ((s.index_le_adjacent k n).trans_lt (s.balanced_succ k n))

/-- A word with arbitrary signed integral exponents in the stage enumeration,
supported only on regular generators. -/
structure Word (s : Schedule) where
  exponent : ℕ →₀ ℤ
  regular : ∀ j, exponent j ≠ 0 → ∃ g, s.stage g = j

namespace Word

variable {s : Schedule}

def q (w : Word s) (k : Bool) : ℕ →₀ ℤ :=
  w.exponent.comapDomain (fun n => s.stage (.adjacent k n))
    (fun _ _ _ _ h => (Generator.adjacent.inj (s.injective h)).2)

def minus (w : Word s) (k : Bool) (n : ℕ) : ℤ := w.exponent (s.stage (.balanced k n))

def plus (w : Word s) (k : Bool) (n : ℕ) : ℤ :=
  w.minus k n + DyadicColumns.adjacent (w.q k) n

/-- Coordinatewise effectiveness and the fixed bound inherited from a divisor
of a single element. -/
def Bounded (w : Word s) (h : ℕ) : Prop :=
  ∀ k n, (0 ≤ w.plus k n ∧ w.plus k n ≤ h) ∧ (0 ≤ w.minus k n ∧ w.minus k n ≤ h)

def AvoidsPrefix (w : Word s) (N : ℕ) : Prop :=
  ∀ k n, n ≤ N → w.plus k n = 0 ∧ w.minus k n = 0

/-- Backward induction from the vanishing tail of `q` gives the sharp bound
`|qₙ| ≤ h` from `2qₙ - qₙ₊₁ = aₙ₊₁ - bₙ₊₁`. -/
theorem abs_q_le (w : Word s) {h : ℕ} (hb : w.Bounded h) (k : Bool) (n : ℕ) :
    |w.q k n| ≤ h := by
  have step (j : ℕ) (hj : |w.q k (j+1)| ≤ h) : |w.q k j| ≤ h := by
    have hv := hb k (j+1)
    simp only [plus, DyadicColumns.adjacent_succ] at hv
    obtain ⟨_, _⟩ := abs_le.mp hj
    apply abs_le.mpr
    omega
  have descend (m d : ℕ) (hd : |w.q k (m+d)| ≤ h) : |w.q k m| ≤ h := by
    induction d generalizing m with
    | zero => simpa using hd
    | succ d ih =>
      exact step m (ih (m+1) (by rwa [show m+1+d = m+(d+1) by omega]))
  let m := (w.q k).support.sup id
  apply descend n (m+1)
  have hz : w.q k (n+(m+1)) = 0 := by
    by_contra hn
    have he : n+(m+1) ≤ m := Finset.le_sup (f := id) (Finsupp.mem_support_iff.mpr hn)
    omega
  simp [hz]

theorem exponent_bound (w : Word s) {h : ℕ} (hb : w.Bounded h) (j : ℕ) :
    |w.exponent j| ≤ h := by
  by_cases hz : w.exponent j = 0
  · simp [hz]
  obtain ⟨g, rfl⟩ := w.regular j hz
  cases g with
  | balanced k n =>
    change |w.minus k n| ≤ _
    rw [abs_of_nonneg (hb k n).2.1]
    exact (hb k n).2.2
  | adjacent k n => exact w.abs_q_le hb k n

theorem exponent_zero_before (w : Word s) {N : ℕ} (hp : w.AvoidsPrefix N)
    (j : ℕ) (hj : j ≤ N) : w.exponent j = 0 := by
  have hq (k : Bool) (n : ℕ) (hn : n ≤ N) : w.q k n = 0 := by
    induction n with
    | zero =>
      have hv := hp k 0 hn
      simp only [plus, DyadicColumns.adjacent_zero] at hv
      omega
    | succ n ih =>
      have hv := hp k (n+1) hn
      simp only [plus, DyadicColumns.adjacent_succ] at hv
      have := ih (by omega)
      omega
  by_contra hz
  obtain ⟨g, rfl⟩ := w.regular j hz
  apply hz
  cases g with
  | balanced k n => exact (hp k n ((s.index_le_balanced k n).trans hj)).2
  | adjacent k n => exact hq k n ((s.index_le_adjacent k n).trans hj)

/-- A latest adjacent exponent contributes twice its value at the next plus
site. Both other columns at that site occur strictly later. -/
theorem latest_positive (w : Word s) {h : ℕ} (hb : w.Bounded h) (j : ℕ)
    (hne : w.exponent j ≠ 0) (hl : ∀ l, j < l → w.exponent l = 0) :
    0 < w.exponent j := by
  obtain ⟨g, rfl⟩ := w.regular j hne
  cases g with
  | balanced k n =>
    exact lt_of_le_of_ne (hb k n).2.1 (Ne.symm hne)
  | adjacent k n =>
    have hm : w.minus k (n+1) = 0 := hl _ (s.balanced_succ k n)
    have hq : w.q k (n+1) = 0 := hl _ (s.adjacent_succ k n)
    have ha := (hb k (n+1)).1.1
    rw [plus, DyadicColumns.adjacent_succ, hm, hq] at ha
    change w.q k n ≠ 0 at hne
    change 0 < w.q k n
    omega

/-- A word with a nonempty profile outside a prefix belongs to the actual
stage list at its latest nonzero index. The output retains the fixed bound. -/
theorem exists_listed_word (w : Word s) (h N : ℕ) (hb : w.Bounded h)
    (hp : w.AvoidsPrefix (max N h)) (hne : ∃ k n, w.plus k n ≠ 0 ∨ w.minus k n ≠ 0) :
    ∃ j > N, ∃ v : RawWords.StageWord j (j+1),
      (∀ i < j, v.oldExponent i = w.exponent i) ∧ (v.latestExponent : ℤ) = w.exponent j ∧
      (∀ i > j, w.exponent i = 0) ∧ v.latestExponent ≤ h ∧ ∀ i, |v.oldExponent i| ≤ h := by
  have hs : w.exponent.support.Nonempty := by
    by_contra he
    have hz : w.exponent = 0 := Finsupp.support_eq_empty.mp (Finset.not_nonempty_iff_eq_empty.mp he)
    obtain ⟨k, n, hn⟩ := hne
    have hq : w.q k = 0 := by ext i; change w.exponent _ = 0; simp [hz]
    simp [plus, minus, hz, hq] at hn
  let j := w.exponent.support.max' hs
  have hj : w.exponent j ≠ 0 := Finsupp.mem_support_iff.mp (Finset.max'_mem _ _)
  have hl (i : ℕ) (hi : j < i) : w.exponent i = 0 := by
    by_contra hn
    exact (Nat.not_le_of_lt hi) (Finset.le_max' _ _ (Finsupp.mem_support_iff.mpr hn))
  have he : max N h < j := Nat.lt_of_not_ge (fun hle => hj (w.exponent_zero_before hp j hle))
  obtain ⟨v, hv, ha⟩ := StageExponents.exists_stageWord_of_latest w.exponent j h
    (w.latest_positive hb j hj hl) (w.exponent_bound hb) (by omega)
  refine ⟨j, by omega, v, hv, ha, hl, ?_, ?_⟩
  · have hbound := (abs_le.mp (w.exponent_bound hb j)).2
    omega
  · intro i
    by_cases hi : i < j
    · rw [hv i hi]
      exact w.exponent_bound hb i
    · simp [RawWords.StageWord.oldExponent, hi]

end Word

/-- Signed realizations of bounded regular profiles avoiding arbitrary finite
prefixes give one sequence of actual elements of the same subring on the stage
lists. The geometric and conductor estimates can use the same sequence. -/
theorem exists_bounded_escaping_listed_sequence {R K : Type*} [CommRing R] [Field K]
    (f : R →+* K) (T : Subring R) (W : ℕ → K) (s : Schedule) (h : ℕ)
    (hextract : ∀ N : ℕ, ∃ y : T, ∃ w : Word s,
      (f (y : R) = w.exponent.prod (fun j z => W j ^ z) ∨
       f (y : R) = -(w.exponent.prod (fun j z => W j ^ z))) ∧
      w.Bounded h ∧ w.AvoidsPrefix N ∧ (∃ k n, w.plus k n ≠ 0 ∨ w.minus k n ≠ 0)) :
    ∃ y : ℕ → T, ∃ stage : ℕ → ℕ, ∃ v : ∀ i, RawWords.StageWord (stage i) (stage i+1),
      (∀ i, i < stage i) ∧ Filter.Tendsto stage Filter.atTop Filter.atTop ∧
      (∀ i, (v i).latestExponent ≤ h) ∧ (∀ i j, |(v i).oldExponent j| ≤ h) ∧
      ∀ i, f (y i : R) = W (stage i) ^ (v i).latestExponent *
        ∏ j ∈ Finset.range (stage i), W j ^ (v i).oldExponent j := by
  have hc (i : ℕ) : ∃ y : T, ∃ j, ∃ v : RawWords.StageWord j (j+1),
      i < j ∧ v.latestExponent ≤ h ∧ (∀ l, |v.oldExponent l| ≤ h) ∧
      f (y : R) = W j ^ v.latestExponent * ∏ l ∈ Finset.range j, W l ^ v.oldExponent l := by
    obtain ⟨y, w, hy, hb, hp, hn⟩ := hextract (max i h)
    obtain ⟨j, hij, v, hv, ha, hl, hb', hv'⟩ := w.exists_listed_word h i hb hp hn
    have he := StageExponents.prod_eq_listed_word W w.exponent j (j+1) v hv ha hl
    rcases hy with hy | hy
    · exact ⟨y, j, v, hij, hb', hv', hy.trans he⟩
    · refine ⟨-y, j, v, hij, hb', hv', ?_⟩
      change f (-(y : R)) = _
      rw [map_neg, hy, neg_neg, he]
  choose y stage v hi hp hb hw using hc
  refine ⟨y, stage, v, hi, ?_, hp, hb, hw⟩
  exact Filter.tendsto_atTop_atTop.mpr fun N => ⟨N, fun i hNi => hNi.trans (hi i).le⟩

end UnconditionalCounterexample.DyadicEscape
