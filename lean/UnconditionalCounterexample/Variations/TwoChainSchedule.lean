import UnconditionalCounterexample.PrimaryWordProfiles

/-!
# Interleaved raw stages and signed words at two centres

The initial two stages introduce the b-seeds. Each subsequent block assigns
b and q for the first colour and then b and q for the second.
Both primary profiles of a mixed word are computed from its single vector
of raw-stage exponents.
-/

namespace UnconditionalCounterexample.Variations.TwoChainSchedule

open NormalizedWords PrimaryWordProfiles PrincipalProfiles WithZero

/-- The number of the raw polynomial realizing a generator. -/
def stage (c : Bool) : Generator → ℕ
  | .b 0 => c.toNat
  | .b (n + 1) => 4 * n + 2 + 2 * c.toNat
  | .q n => 4 * n + 3 + 2 * c.toNat

/-- The chronological order within each colour is the original one-centre order. -/
theorem stage_lt_of_lt (c : Bool) {i j : Generator} (h : i.stage < j.stage) :
    stage c i < stage c j := by
  rcases i with (_ | n) | n <;> rcases j with (_ | m) | m <;>
    cases c <;> simp_all [stage, Generator.stage] <;> omega

theorem local_stage_le (c : Bool) (i : Generator) : i.stage ≤ stage c i := by
  rcases i with (_ | n) | n <;> cases c <;> simp [stage, Generator.stage] <;> omega

theorem stage_injective {c d : Bool} {i j : Generator} (h : stage c i = stage d j) :
    c = d ∧ i = j := by
  rcases i with (_ | n) | n <;> rcases j with (_ | m) | m <;>
    cases c <;> cases d <;> simp_all [stage] <;> omega

theorem stage_surjective (i : ℕ) : ∃ c j, stage c j = i := by
  rcases i with _ | _ | i
  · exact ⟨false, .b 0, rfl⟩
  · exact ⟨true, .b 0, rfl⟩
  · rcases (show i % 4 = 0 ∨ i % 4 = 1 ∨ i % 4 = 2 ∨ i % 4 = 3 by omega) with h | h | h | h
    · exact ⟨false, .b (i / 4 + 1), by simp [stage]; omega⟩
    · exact ⟨false, .q (i / 4), by simp [stage]; omega⟩
    · exact ⟨true, .b (i / 4 + 1), by simp [stage]; omega⟩
    · exact ⟨true, .q (i / 4), by simp [stage]; omega⟩

/-- Bijection decoding a raw stage into its colour and local generator. -/
noncomputable def decode : ℕ ≃ Bool × Generator :=
  (Equiv.ofBijective (fun p : Bool × Generator => stage p.1 p.2)
    ⟨fun p q h => Prod.ext (stage_injective h).1 (stage_injective h).2,
      fun k => by obtain ⟨c, i, rfl⟩ := stage_surjective k; exact ⟨(c, i), rfl⟩⟩).symm

@[simp] theorem decode_stage (c : Bool) (i : Generator) : decode (stage c i) = (c, i) :=
  decode.apply_symm_apply (c, i)

@[simp] theorem stage_decode (k : ℕ) : stage (decode k).1 (decode k).2 = k :=
  decode.symm_apply_apply k

/-- Weight of the raw generator at stage `i` in the primary coordinate `j`
of colour `c`. Written by rows so a finite word reads off its own exponents. -/
def weight (i : ℕ) (c : Bool) : ℕ → ℤ
  | 0 => (if i = stage c (.b 0) then 3 else 0) +
         (if i = stage c (.q 0) then 2 else 0)
  | j + 1 =>
    if j % 2 = 0 then (if i = stage c (.q (j / 2)) then 1 else 0)
    else (if i = stage c (.b (j / 2 + 1)) then 3 else 0) +
         (if i = stage c (.q (j / 2 + 1)) then 2 else 0) +
         (if i = stage c (.q (j / 2)) then 2 else 0)

@[simp] theorem weight_odd (i : ℕ) (c : Bool) (n : ℕ) :
    weight i c (2*n+1) = if i = stage c (.q n) then 1 else 0 := by
  simp [weight]

@[simp] theorem weight_even (i : ℕ) (c : Bool) (n : ℕ) :
    weight i c (2*n+2) = (if i = stage c (.b (n+1)) then 3 else 0) +
      (if i = stage c (.q (n+1)) then 2 else 0) + (if i = stage c (.q n) then 2 else 0) := by
  simp [weight, show (2*n+1) / 2 = n by omega]

private theorem stage_eq_iff {c d : Bool} {i j : Generator} :
    stage c i = stage d j ↔ c = d ∧ i = j :=
  ⟨stage_injective, fun ⟨rfl, rfl⟩ => rfl⟩

/-- The b-columns are the ternary singletons on their own colour. -/
theorem weight_b (c d : Bool) (n j : ℕ) : weight (stage c (.b n)) d j =
    if c = d then bWeight n j else 0 := by
  by_cases h : c = d
  · subst d
    rcases (show j = 0 ∨ j = 2*(j/2)+1 ∨ j = 2*((j-2)/2)+2 by omega) with hj | hj | hj
    · subst j
      simp [weight, stage_eq_iff, bWeight]
    · conv_lhs => rw [hj, weight_odd]
      simp [stage_eq_iff, bWeight]
      omega
    · conv_lhs => rw [hj, weight_even]
      simp [stage_eq_iff, bWeight]
      split_ifs <;> omega
  · rcases (show j = 0 ∨ j = 2*(j/2)+1 ∨ j = 2*((j-2)/2)+2 by omega) with hj | hj | hj
    · simp [hj, weight, stage_eq_iff, h]
    · conv_lhs => rw [hj, weight_odd]
      simp [stage_eq_iff, h]
    · conv_lhs => rw [hj, weight_even]
      simp [stage_eq_iff, h]

/-- The q-columns have weights (2,1,2) on consecutive sites of their own colour. -/
theorem weight_q (c d : Bool) (n j : ℕ) : weight (stage c (.q n)) d j =
    if c = d then qWeight n j else 0 := by
  by_cases h : c = d
  · subst d
    rcases (show j = 0 ∨ j = 2*(j/2)+1 ∨ j = 2*((j-2)/2)+2 by omega) with hj | hj | hj
    · subst j
      simp [weight, stage_eq_iff, qWeight]
    · conv_lhs => rw [hj, weight_odd]
      simp [stage_eq_iff, qWeight]
      split_ifs <;> omega
    · conv_lhs => rw [hj, weight_even]
      simp [stage_eq_iff, qWeight]
      split_ifs <;> omega
  · rcases (show j = 0 ∨ j = 2*(j/2)+1 ∨ j = 2*((j-2)/2)+2 by omega) with hj | hj | hj
    · simp [hj, weight, stage_eq_iff, h]
    · conv_lhs => rw [hj, weight_odd]
      simp [stage_eq_iff, h]
    · conv_lhs => rw [hj, weight_even]
      simp [stage_eq_iff, h]

/-- Allocation stage for an X- or Y-primary, in the order X₀,Y₀,X₁,Y₁,…. -/
def allocationStage (c : Bool) (i : ℕ) : ℕ :=
  if i % 2 = 0 then stage c (.b (i / 2)) else stage c (.q (i / 2))

@[simp] theorem allocationStage_even (c : Bool) (n : ℕ) :
    allocationStage c (2*n) = stage c (.b n) := by simp [allocationStage]

@[simp] theorem allocationStage_odd (c : Bool) (n : ℕ) :
    allocationStage c (2*n+1) = stage c (.q n) := by
  simp [allocationStage, show (2*n+1)/2 = n by omega]

/-- No raw generator has a prescribed nonzero order at an unallocated site. -/
theorem allocationStage_le_of_weight_ne_zero {k j : ℕ} {d : Bool} (h : weight k d j ≠ 0) :
    allocationStage d j ≤ k := by
  obtain ⟨c, g, rfl⟩ := stage_surjective k
  cases g with
  | b n =>
    rw [weight_b] at h
    by_cases heq : c = d
    · subst c
      have hj : j = 2*n := by simpa [bWeight] using h
      simp [hj]
    · simp [heq] at h
  | q n =>
    rw [weight_q] at h
    by_cases heq : c = d
    · subst c
      have hj : j = 2*n ∨ j = 2*n+1 ∨ j = 2*n+2 := by
        by_contra! hh
        simp [qWeight, hh.1, hh.2.1, hh.2.2] at h
      rcases hj with rfl | rfl | rfl
      · rw [allocationStage_even]
        cases n <;> cases d <;> simp [stage] <;> omega
      · simp
      · rw [show 2*n+2 = 2*(n+1) by omega, allocationStage_even]
        simp [stage]
    · simp [heq] at h

/-- Compute both profiles of one actual signed product of the interleaved
generators. Opposite-colour factors contribute zero to the additive order. -/
theorem represents_signed_word {K : Type*} [Field K] (v : Bool → ℕ → Valuation K ℤᵐ⁰)
    (W : ℕ → K) (hw : ∀ c j i, v c j (W i) = exp (-weight i c j))
    (e : ℕ →₀ ℤ) (x : K) (hx : x = word W e ∨ x = -word W e)
    (g : Bool → ℕ → ℤ) (hg : ∀ c j, v c j x = exp (-g c j)) (c : Bool) :
    Represents (fun n => e (stage c (.b n))) (fun n => e (stage c (.q n))) (g c) := by
  have hsum (j : ℕ) : g c j = e.sum (fun i z => z * weight i c j) := by
    have h := valuation_word (v c j) W _ (hw c j) e
    have he := hg c j
    rcases hx with rfl | rfl
    · exact neg_injective (exp_injective (he.symm.trans h))
    · rw [Valuation.map_neg] at he
      exact neg_injective (exp_injective (he.symm.trans h))
  constructor
  · rw [hsum]
    simp only [weight, mul_add, Finsupp.sum_add, sum_indicator]
    ring
  · intro n
    rw [hsum]
    simp only [weight_odd, sum_indicator, mul_one]
  · intro n
    rw [hsum]
    simp only [weight_even, mul_add, Finsupp.sum_add, sum_indicator]
    ring

/-- The maximum nonzero raw stage of a bounded effective mixed word has
positive exponent. If both primary prefixes vanish it lies beyond the chosen
cutoff. The uniform bound applies also to all earlier signed coefficients. -/
theorem bounded_latest_beyond (e : ℕ →₀ ℤ) (g : Bool → ℕ → ℤ)
    (hrep : ∀ c, Represents (fun n => e (stage c (.b n))) (fun n => e (stage c (.q n))) (g c))
    {r : ℤ} (hbound : ∀ c i, 0 ≤ g c i ∧ g c i ≤ r) (hnonzero : ∃ c i, g c i ≠ 0)
    (N : ℕ) (hzero : ∀ c i, i < 2*N+2 → g c i = 0) :
    ∃ k, N < k ∧ 0 < e k ∧ (∀ i, |e i| ≤ 2*r) ∧ ∀ i, k < i → e i = 0 := by
  obtain ⟨c, i, hi⟩ := hnonzero
  obtain ⟨gen, hgen⟩ := exists_nonzero_exponent (hrep c) ⟨i, hi⟩
  have hexp (d : Bool) (j : Generator) :
      j.exponent (fun n => e (stage d (.b n))) (fun n => e (stage d (.q n))) =
      e (stage d j) := by cases j <;> rfl
  rw [hexp] at hgen
  let k := e.support.max' ⟨_, Finsupp.mem_support_iff.mpr hgen⟩
  have hk : e k ≠ 0 := Finsupp.mem_support_iff.mp (Finset.max'_mem ..)
  have hlate (i : ℕ) (hi : k < i) : e i = 0 := by
    apply Finsupp.notMem_support_iff.mp
    exact fun hmem => (Finset.le_max' _ _ hmem).not_gt hi
  obtain ⟨d, j, hj⟩ := stage_surjective k
  have hjnz : j.exponent (fun n => e (stage d (.b n))) (fun n => e (stage d (.q n))) ≠ 0 := by
    rwa [hexp, hj]
  have hpos := exponent_pos_of_latest (hrep d) (fun l => (hbound d l).1) j hjnz (by
    intro a ha
    rw [hexp]
    exact hlate _ (hj ▸ stage_lt_of_lt d ha))
  rw [hexp, hj] at hpos
  refine ⟨k, ?_, hpos, ?_, hlate⟩
  · by_contra h
    apply hjnz
    exact stage_exponents_zero_of_profile_prefix (hrep d) N (hzero d) j
      ((local_stage_le d j).trans (by omega))
  · intro t
    obtain ⟨a, w, rfl⟩ := stage_surjective t
    rw [← hexp a w]
    exact generator_exponent_bound (hrep a) (hbound a) w

/-- With the stage's built-in exponent budget, the mixed product is literally
one of the listed words. The bounds used for conductor transfer stay uniform
as the stages grow. -/
theorem exists_listed_word_beyond {K : Type*} [Field K] (W : ℕ → K)
    (e : ℕ →₀ ℤ) (g : Bool → ℕ → ℤ)
    (hrep : ∀ c, Represents (fun n => e (stage c (.b n))) (fun n => e (stage c (.q n))) (g c))
    (r N : ℕ) (hbound : ∀ c i, 0 ≤ g c i ∧ g c i ≤ r) (hnonzero : ∃ c i, g c i ≠ 0)
    (hzero : ∀ c i, i < 2 * max N (2*r) + 2 → g c i = 0) :
    ∃ k > N, ∃ w : RawWords.StageWord k (k+1), w.latestExponent ≤ 2*r ∧
      (∀ j, |w.oldExponent j| ≤ (2*r : ℕ)) ∧
      word W e = W k ^ w.latestExponent * ∏ j ∈ Finset.range k, W j ^ w.oldExponent j := by
  obtain ⟨k, hk, hp, hb, hl⟩ := bounded_latest_beyond e g hrep hbound hnonzero _ hzero
  have hb' : ∀ j, |e j| ≤ (2*r : ℕ) := by simpa only [Nat.cast_mul, Nat.cast_ofNat] using hb
  obtain ⟨w, hw, hwe⟩ := StageExponents.exists_stageWord_of_latest e k (2*r) hp hb' (by omega)
  refine ⟨k, by omega, w, ?_, ?_, StageExponents.prod_eq_listed_word W e k _ w hw hwe hl⟩
  · have he := abs_le.mp (hb' k)
    omega
  · intro j
    by_cases hj : j < k
    · rw [hw j hj]
      exact hb' j
    · simp [RawWords.StageWord.oldExponent, hj]

end UnconditionalCounterexample.Variations.TwoChainSchedule
