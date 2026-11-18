import HereditaryAtomicity.DVRBase.MovingWindows

/-!
# Numerical orders in the finite Laurent model

These level-value inequalities hold for an arbitrary real coefficient order,
independently of the coefficient field.
-/

namespace HereditaryAtomicity.DVRBase

open scoped BigOperators

variable {n : ℕ}

/-- Sum of coordinates strictly before a cut, in the zero-based indexing. -/
def prefixSum (f : Fin n → ℝ) (k : ℕ) : ℝ :=
  ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < k), f i

@[simp] theorem prefixSum_zero (f : Fin n → ℝ) : prefixSum f 0 = 0 := by
  simp [prefixSum]

@[simp] theorem prefixSum_top (f : Fin n → ℝ) : prefixSum f n = ∑ i, f i := by
  simp [prefixSum]

theorem prefixSum_succ (f : Fin n → ℝ) {k : ℕ} (hk : k < n) :
    prefixSum f (k + 1) = prefixSum f k + f ⟨k, hk⟩ := by
  have hset : (Finset.univ.filter fun i : Fin n => i.val < k + 1) =
      insert ⟨k, hk⟩ (Finset.univ.filter fun i : Fin n => i.val < k) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Fin.ext_iff]
    omega
  have hnot : (⟨k, hk⟩ : Fin n) ∉ Finset.univ.filter (fun i : Fin n => i.val < k) := by
    simp
  simp only [prefixSum, hset, Finset.sum_insert hnot]
  ring

theorem prefixSum_add (f g : Fin n → ℝ) (k : ℕ) :
    prefixSum (fun i => f i + g i) k = prefixSum f k + prefixSum g k := by
  simp [prefixSum, Finset.sum_add_distrib]

/-- Coefficient order plus the weighted exponents before the cut. -/
def partialValue (u : Fin n → ℝ) (e : ℝ) (β : Fin n → ℤ) (k : ℕ) : ℝ :=
  e + prefixSum (fun i => (β i : ℝ) * u i) k

/-- The value of the chain endpoint at a cut. -/
def remainingValue (u : Fin n → ℝ) (κ : ℝ) (k : ℕ) : ℝ :=
  κ - prefixSum u k

/-- Partial order corrected by all poles strictly after the cut. -/
def levelValue (u : Fin n → ℝ) (κ e : ℝ) (β : Fin n → ℤ) (k : ℕ) : ℝ :=
  partialValue u e β k - (poleTail β k : ℝ) * remainingValue u κ k

@[simp] theorem partialValue_zero (u : Fin n → ℝ) (e : ℝ) (β : Fin n → ℤ) :
    partialValue u e β 0 = e := by simp [partialValue]

@[simp] theorem remainingValue_zero (u : Fin n → ℝ) (κ : ℝ) :
    remainingValue u κ 0 = κ := by simp [remainingValue]

theorem partialValue_succ (u : Fin n → ℝ) (e : ℝ) (β : Fin n → ℤ)
    {k : ℕ} (hk : k < n) :
    partialValue u e β (k + 1) = partialValue u e β k + (β ⟨k, hk⟩ : ℝ) * u ⟨k, hk⟩ := by
  simp [partialValue, prefixSum_succ _ hk, add_assoc]

theorem remainingValue_succ (u : Fin n → ℝ) (κ : ℝ) {k : ℕ} (hk : k < n) :
    remainingValue u κ (k + 1) = remainingValue u κ k - u ⟨k, hk⟩ := by
  simp [remainingValue, prefixSum_succ _ hk]
  ring

theorem poleTail_step (β : Fin n → ℤ) {k : ℕ} (hk : k < n) :
    poleTail β k = max (poleTail β (k + 1)) (-β ⟨k, hk⟩) := by
  apply le_antisymm
  · apply (poleTail_le_iff β k _).mpr
    refine ⟨(poleTail_nonneg β (k + 1)).trans (le_max_left _ _), ?_⟩
    intro i hi
    by_cases he : i.val = k
    · have hei : i = ⟨k, hk⟩ := Fin.ext he
      simpa only [hei] using le_max_right (poleTail β (k + 1)) (-β ⟨k, hk⟩)
    · exact (neg_le_poleTail β i (by omega)).trans (le_max_left _ _)
  · exact max_le (poleTail_antitone β (Nat.le_succ k)) (neg_le_poleTail β ⟨k, hk⟩ le_rfl)

theorem poleTail_add_le (β γ : Fin n → ℤ) (k : ℕ) :
    poleTail (β + γ) k ≤ poleTail β k + poleTail γ k := by
  apply (poleTail_le_iff (β + γ) k _).mpr
  refine ⟨add_nonneg (poleTail_nonneg β k) (poleTail_nonneg γ k), ?_⟩
  intro i hi
  have hb := neg_le_poleTail β i hi
  have hg := neg_le_poleTail γ i hi
  simp only [Pi.add_apply]
  omega

theorem poleTail_eq_zero_iff (β : Fin n → ℤ) (k : ℕ) :
    poleTail β k = 0 ↔ ∀ i : Fin n, k ≤ i.val → 0 ≤ β i := by
  constructor
  · intro h i hi
    have h' := neg_le_poleTail β i hi
    rw [h] at h'
    omega
  · intro h
    apply le_antisymm _ (poleTail_nonneg β k)
    apply (poleTail_le_iff β k 0).mpr
    exact ⟨le_rfl, fun i hi => by have := h i hi; omega⟩

@[simp] theorem poleTail_zero (k : ℕ) : poleTail (0 : Fin n → ℤ) k = 0 :=
  (poleTail_eq_zero_iff 0 k).mpr (by intro i _; simp)

theorem poleTail_eq_zero_of_nonneg (β : Fin n → ℤ) (hβ : ∀ i, 0 ≤ β i) (k : ℕ) :
    poleTail β k = 0 := (poleTail_eq_zero_iff β k).mpr (fun i _ => hβ i)

theorem poleTail_const (a : ℤ) {k : ℕ} (hk : k < n) :
    poleTail (fun _ : Fin n => a) k = max 0 (-a) := by
  apply le_antisymm
  · exact (poleTail_le_iff _ k _).mpr ⟨le_max_left _ _, fun _ _ => le_max_right _ _⟩
  · exact max_le (poleTail_nonneg _ k)
      (neg_le_poleTail (fun _ : Fin n => a) (k := k) ⟨k, hk⟩ le_rfl)

@[simp] theorem partialValue_zero_exponent (u : Fin n → ℝ) (e : ℝ) (k : ℕ) :
    partialValue u e 0 k = e := by simp [partialValue, prefixSum]

@[simp] theorem levelValue_zero_exponent (u : Fin n → ℝ) (κ e : ℝ) (k : ℕ) :
    levelValue u κ e 0 k = e := by simp [levelValue]

theorem partialValue_eq_total_of_tail_zero (u : Fin n → ℝ) (e : ℝ)
    (β : Fin n → ℤ) (k : ℕ) (hβ : ∀ i : Fin n, k ≤ i.val → β i = 0) :
    partialValue u e β k = e + ∑ i, (β i : ℝ) * u i := by
  unfold partialValue prefixSum
  congr 1
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro i _ hi
  have hik : k ≤ i.val := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hi
    exact hi
  simp [hβ i hik]

@[simp] theorem levelValue_top (u : Fin n → ℝ) (κ e : ℝ) (β : Fin n → ℤ) :
    levelValue u κ e β n = e + ∑ i, (β i : ℝ) * u i := by
  simp [levelValue, partialValue]

theorem levelValue_le_succ (u : Fin n → ℝ) (κ e : ℝ) (β : Fin n → ℤ)
    {k : ℕ} (hk : k < n) (hu : 0 ≤ u ⟨k, hk⟩)
    (hs : 0 ≤ remainingValue u κ (k + 1)) :
    levelValue u κ e β k ≤ levelValue u κ e β (k + 1) := by
  have hb : 0 ≤ (β ⟨k, hk⟩ : ℝ) + (poleTail β k : ℝ) := by
    have h : -β ⟨k, hk⟩ ≤ poleTail β k := neg_le_poleTail β (k := k) ⟨k, hk⟩ le_rfl
    exact_mod_cast (show 0 ≤ β ⟨k, hk⟩ + poleTail β k by omega)
  have hd : 0 ≤ (poleTail β k : ℝ) - (poleTail β (k + 1) : ℝ) := by
    exact_mod_cast sub_nonneg.mpr (poleTail_antitone β (Nat.le_succ k))
  have hs' := remainingValue_succ u κ hk
  have hs0 : remainingValue u κ k = remainingValue u κ (k + 1) + u ⟨k, hk⟩ := by
    linarith
  have hp := partialValue_succ u e β hk
  have h1 := mul_nonneg hb hu
  have h2 := mul_nonneg hd hs
  dsimp [levelValue]
  rw [hp, hs0]
  nlinarith only [h1, h2]

theorem levelValue_mono (u : Fin n → ℝ) (κ e : ℝ) (β : Fin n → ℤ)
    (hu : ∀ i, 0 ≤ u i) (hs : ∀ k ≤ n, 0 ≤ remainingValue u κ k)
    {k l : ℕ} (hkl : k ≤ l) (hl : l ≤ n) :
    levelValue u κ e β k ≤ levelValue u κ e β l := by
  induction l with
  | zero =>
      have hk : k = 0 := by omega
      subst k
      exact le_rfl
  | succ l ih =>
      by_cases he : k = l + 1
      · subst k; exact le_rfl
      · have hkn : k ≤ l := by omega
        have hln : l < n := by omega
        exact (ih hkn (by omega)).trans (levelValue_le_succ u κ e β hln (hu _) (hs _ hl))

theorem partialValue_add (u : Fin n → ℝ) (e f : ℝ) (β γ : Fin n → ℤ) (k : ℕ) :
    partialValue u (e + f) (β + γ) k = partialValue u e β k + partialValue u f γ k := by
  simp [partialValue, prefixSum, Int.cast_add, add_mul, Finset.sum_add_distrib]
  ring

theorem levelValue_add_ge (u : Fin n → ℝ) (κ e f : ℝ) (β γ : Fin n → ℤ)
    (k : ℕ) (hs : 0 ≤ remainingValue u κ k) :
    levelValue u κ e β k + levelValue u κ f γ k ≤ levelValue u κ (e + f) (β + γ) k := by
  have hd : (poleTail (β + γ) k : ℝ) ≤ (poleTail β k : ℝ) + (poleTail γ k : ℝ) := by
    exact_mod_cast poleTail_add_le β γ k
  have hmul := mul_le_mul_of_nonneg_right hd hs
  simp only [levelValue, partialValue_add]
  nlinarith

theorem levelValue_mono_coefficient (u : Fin n → ℝ) (κ : ℝ) (β : Fin n → ℤ)
    (k : ℕ) {e f : ℝ} (hef : e ≤ f) :
    levelValue u κ e β k ≤ levelValue u κ f β k := by
  dsimp [levelValue, partialValue]
  linarith

/-- The level test for membership of a monomial in R₀. -/
def MeetsLevel (u : Fin n → ℝ) (κ : ℝ) (T : ℕ → ℝ) (β : Fin n → ℤ) (e : ℝ) : Prop :=
  ∃ k ≤ n, T k ≤ levelValue u κ e β k

theorem MeetsLevel.upward {u : Fin n → ℝ} {κ : ℝ} {T : ℕ → ℝ}
    {β : Fin n → ℤ} {e f : ℝ} (h : MeetsLevel u κ T β e) (hef : e ≤ f) :
    MeetsLevel u κ T β f := by
  obtain ⟨k, hk, h⟩ := h
  exact ⟨k, hk, h.trans (levelValue_mono_coefficient u κ β k hef)⟩

theorem MeetsLevel.of_nonneg {u : Fin n → ℝ} {κ : ℝ} {T : ℕ → ℝ}
    {β : Fin n → ℤ} {e : ℝ} (hT : T 0 ≤ 0) (he : 0 ≤ e)
    (hβ : ∀ i, 0 ≤ β i) : MeetsLevel u κ T β e := by
  refine ⟨0, Nat.zero_le _, ?_⟩
  have hp : poleTail β 0 = 0 := (poleTail_eq_zero_iff β 0).mpr (fun i _ => hβ i)
  simpa [levelValue, hp] using hT.trans he

theorem MeetsLevel.of_tail_zero {u : Fin n → ℝ} {κ : ℝ} {T : ℕ → ℝ}
    {β : Fin n → ℤ} {e : ℝ} {k : ℕ} (hk : k ≤ n)
    (hβ : ∀ i : Fin n, k ≤ i.val → β i = 0)
    (he : T k ≤ e + ∑ i, (β i : ℝ) * u i) : MeetsLevel u κ T β e := by
  refine ⟨k, hk, ?_⟩
  have hp : poleTail β k = 0 :=
    (poleTail_eq_zero_iff β k).mpr (fun i hi => by simp [hβ i hi])
  simpa [levelValue, hp, partialValue_eq_total_of_tail_zero u e β k hβ] using he

theorem MeetsLevel.add {u : Fin n → ℝ} {κ : ℝ} {T : ℕ → ℝ}
    (hu : ∀ i, 0 ≤ u i) (hs : ∀ k ≤ n, 0 ≤ remainingValue u κ k)
    (hT : ∀ k ≤ n, 0 ≤ T k) {β γ : Fin n → ℤ} {e f : ℝ}
    (he : MeetsLevel u κ T β e) (hf : MeetsLevel u κ T γ f) :
    MeetsLevel u κ T (β + γ) (e + f) := by
  obtain ⟨k, hk, he⟩ := he
  obtain ⟨l, hl, hf⟩ := hf
  rcases le_total k l with hkl | hlk
  · refine ⟨l, hl, ?_⟩
    have he' := he.trans (levelValue_mono u κ e β hu hs hkl hl)
    have hprod := levelValue_add_ge u κ e f β γ l (hs l hl)
    have hnonneg := hT k hk
    linarith
  · refine ⟨k, hk, ?_⟩
    have hf' := hf.trans (levelValue_mono u κ f γ hu hs hlk hk)
    have hprod := levelValue_add_ge u κ e f β γ k (hs k hk)
    have hnonneg := hT l hl
    linarith

theorem MeetsLevel.nonneg_total {u : Fin n → ℝ} {κ : ℝ} {T : ℕ → ℝ}
    (hu : ∀ i, 0 ≤ u i) (hs : ∀ k ≤ n, 0 ≤ remainingValue u κ k)
    (hT : ∀ k ≤ n, 0 ≤ T k) {β : Fin n → ℤ} {e : ℝ}
    (he : MeetsLevel u κ T β e) : 0 ≤ e + ∑ i, (β i : ℝ) * u i := by
  obtain ⟨k, hk, he⟩ := he
  have hm := levelValue_mono u κ e β hu hs hk (le_refl n)
  rw [levelValue_top] at hm
  exact (hT k hk).trans (he.trans hm)

/-- The prefix factor after extracting a common endpoint power. -/
def modelHeadExponent (β : Fin n → ℤ) (k : ℕ) (i : Fin n) : ℤ :=
  if i.val < k then β i + poleTail β k else 0

/-- The nonnegative tail factor after extracting a common endpoint power. -/
def modelTailExponent (β : Fin n → ℤ) (k : ℕ) (i : Fin n) : ℤ :=
  if k ≤ i.val then β i + poleTail β k else 0

theorem modelHeadExponent_tail (β : Fin n → ℤ) (k : ℕ) (i : Fin n) (hi : k ≤ i.val) :
    modelHeadExponent β k i = 0 := by
  simp [modelHeadExponent, not_lt.mpr hi]

theorem modelTailExponent_prefix (β : Fin n → ℤ) (k : ℕ) (i : Fin n) (hi : i.val < k) :
    modelTailExponent β k i = 0 := by
  simp [modelTailExponent, not_le.mpr hi]

theorem modelTailExponent_nonneg (β : Fin n → ℤ) (k : ℕ) (i : Fin n) :
    0 ≤ modelTailExponent β k i := by
  unfold modelTailExponent
  split_ifs with hi
  · have h := neg_le_poleTail β (k := k) i hi
    omega
  · exact le_rfl

@[simp] theorem modelHeadExponent_zero (β : Fin n → ℤ) : modelHeadExponent β 0 = 0 := by
  funext i
  simp [modelHeadExponent]

/-- Exact exponent identity behind the monomial normal form in Lemma 6.5(b). -/
theorem modelExponent_decomposition (β : Fin n → ℤ) (k : ℕ) :
    modelHeadExponent β k + (fun _ => -poleTail β k) + modelTailExponent β k = β := by
  funext i
  simp only [Pi.add_apply, modelHeadExponent, modelTailExponent]
  by_cases hi : i.val < k
  · simp [hi, not_le.mpr hi]
  · simp [hi, Nat.le_of_not_gt hi]

theorem modelHeadExponent_weight (u : Fin n → ℝ) (β : Fin n → ℤ) (k : ℕ) :
    (∑ i, (modelHeadExponent β k i : ℝ) * u i) =
      prefixSum (fun i => (β i : ℝ) * u i) k + (poleTail β k : ℝ) * prefixSum u k := by
  calc
    _ = ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < k),
        ((β i : ℝ) + (poleTail β k : ℝ)) * u i := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : i.val < k
      · simp [modelHeadExponent, hi]
      · simp [modelHeadExponent, hi]
    _ = _ := by
      simp [prefixSum, add_mul, Finset.sum_add_distrib, Finset.mul_sum]

/-- The prefix factor has exactly the corrected level value, including its
coefficient shifted by the extracted uniformizer power. -/
theorem modelHeadExponent_order (u : Fin n → ℝ) (κ e : ℝ) (β : Fin n → ℤ) (k : ℕ) :
    (e - κ * (poleTail β k : ℝ)) + ∑ i, (modelHeadExponent β k i : ℝ) * u i =
      levelValue u κ e β k := by
  rw [modelHeadExponent_weight]
  unfold levelValue partialValue remainingValue
  ring

/-- Division by the full endpoint monomial adds one to each exponent.
For a nonnegative exponent vector, the quotient has no remaining poles. -/
theorem levelValue_endpoint_quotient (u : Fin n → ℝ) (κ e : ℝ)
    (β : Fin n → ℤ) (hβ : ∀ i, 0 ≤ β i) (k : ℕ) :
    levelValue u κ (e - κ) (fun i => β i + 1) k =
      partialValue u e β k - remainingValue u κ k := by
  have hp : poleTail (fun i => β i + 1) k = 0 :=
    poleTail_eq_zero_of_nonneg _ (fun i => by have := hβ i; omega) k
  simp only [levelValue, hp, Int.cast_zero, zero_mul, sub_zero,
    partialValue, remainingValue, prefixSum, Int.cast_add, Int.cast_one, add_mul, one_mul,
    Finset.sum_add_distrib]
  ring

/-- Dividing by the endpoint converts the membership test into a threshold inequality,
even for nonintegral coefficient orders. -/
theorem meetsLevel_endpoint_quotient_iff (u : Fin n → ℝ) (κ e : ℝ)
    (T : ℕ → ℝ) (β : Fin n → ℤ) (hβ : ∀ i, 0 ≤ β i) :
    MeetsLevel u κ T (fun i => β i + 1) (e - κ) ↔
      ∃ k ≤ n, T k + remainingValue u κ k ≤ partialValue u e β k := by
  unfold MeetsLevel
  simp only [levelValue_endpoint_quotient u κ e β hβ, le_sub_iff_add_le]

/-- If every positive level starts above B, a monomial of total order below B
can meet a level threshold only at the zero cut. -/
theorem MeetsLevel.at_zero_of_total_lt {u : Fin n → ℝ} {κ B : ℝ} {T : ℕ → ℝ}
    (hu : ∀ i, 0 ≤ u i) (hs : ∀ k ≤ n, 0 ≤ remainingValue u κ k)
    (hT : ∀ k, 0 < k → k ≤ n → B ≤ T k) {β : Fin n → ℤ} {e : ℝ}
    (he : MeetsLevel u κ T β e) (hsmall : e + ∑ i, (β i : ℝ) * u i < B) :
    T 0 ≤ levelValue u κ e β 0 := by
  obtain ⟨k, hk, he⟩ := he
  by_cases hk0 : k = 0
  · simpa only [hk0] using he
  · have hkp : 0 < k := Nat.pos_of_ne_zero hk0
    have hm := levelValue_mono u κ e β hu hs hk (le_refl n)
    rw [levelValue_top] at hm
    have ht := hT k hkp hk
    linarith

/-- The zero-cut condition forces a nonnegative coefficient order. -/
theorem coefficient_nonneg_of_zero_level (u : Fin n → ℝ) {κ e : ℝ}
    (hκ : 0 ≤ κ) (β : Fin n → ℤ) (h : 0 ≤ levelValue u κ e β 0) : 0 ≤ e := by
  have hd : (0 : ℝ) ≤ poleTail β 0 := by exact_mod_cast poleTail_nonneg β 0
  simp only [levelValue, partialValue_zero, remainingValue_zero] at h
  nlinarith only [h, mul_nonneg hd hκ]

/-- At coefficient order zero, a positive anchor and the zero-cut condition
force every exponent to be nonnegative. -/
theorem exponent_nonneg_of_zero_coefficient_level (u : Fin n → ℝ) {κ : ℝ}
    (hκ : 0 < κ) (β : Fin n → ℤ) (h : 0 ≤ levelValue u κ 0 β 0) :
    ∀ i, 0 ≤ β i := by
  have hd : (0 : ℝ) ≤ poleTail β 0 := by exact_mod_cast poleTail_nonneg β 0
  have hz : (poleTail β 0 : ℝ) = 0 := by
    simp only [levelValue, partialValue_zero, remainingValue_zero] at h
    nlinarith
  have hz' : poleTail β 0 = 0 := by exact_mod_cast hz
  exact fun i => (poleTail_eq_zero_iff β 0).mp hz' i (Nat.zero_le _)

theorem totalOrder_endpoint_quotient (u : Fin n → ℝ) (κ e : ℝ) (β : Fin n → ℤ) :
    (e - κ) + ∑ i, ((β i + 1 : ℤ) : ℝ) * u i =
      (e + ∑ i, (β i : ℝ) * u i) - remainingValue u κ n := by
  simp [remainingValue, Int.cast_add, add_mul, Finset.sum_add_distrib]
  ring

/-- For a monomial of low order in the endpoint ideal, its quotient meets the level-zero
test. -/
theorem endpoint_quotient_zero_level {u : Fin n → ℝ} {κ e : ℝ} {T : ℕ → ℝ}
    (hu : ∀ i, 0 ≤ u i) (hs : ∀ k ≤ n, 0 ≤ remainingValue u κ k)
    (hT0 : T 0 = 0) (hT : ∀ k, 0 < k → k ≤ n → 2 * κ ≤ T k)
    (β : Fin n → ℤ) (hmem : MeetsLevel u κ T (fun i => β i + 1) (e - κ))
    (hsmall : e + ∑ i, (β i : ℝ) * u i < 2 * κ) :
    0 ≤ levelValue u κ (e - κ) (fun i => β i + 1) 0 := by
  have hsmall' : (e - κ) + ∑ i, ((β i + 1 : ℤ) : ℝ) * u i < 2 * κ := by
    rw [totalOrder_endpoint_quotient]
    exact (sub_le_self _ (hs n le_rfl)).trans_lt hsmall
  simpa only [hT0] using hmem.at_zero_of_total_lt hu hs hT hsmall'

/-- The coefficient order of a low-order endpoint-ideal monomial is at least κ. -/
theorem endpoint_coefficient_ge_anchor {u : Fin n → ℝ} {κ e : ℝ} {T : ℕ → ℝ}
    (hu : ∀ i, 0 ≤ u i) (hs : ∀ k ≤ n, 0 ≤ remainingValue u κ k)
    (hκ : 0 ≤ κ) (hT0 : T 0 = 0) (hT : ∀ k, 0 < k → k ≤ n → 2 * κ ≤ T k)
    (β : Fin n → ℤ) (hmem : MeetsLevel u κ T (fun i => β i + 1) (e - κ))
    (hsmall : e + ∑ i, (β i : ℝ) * u i < 2 * κ) : κ ≤ e := by
  have h := coefficient_nonneg_of_zero_level u hκ (fun i => β i + 1)
    (endpoint_quotient_zero_level hu hs hT0 hT β hmem hsmall)
  linarith

/-- Equality in the coefficient bound forces a nonnegative exponent vector
after division by the endpoint monomial. -/
theorem endpoint_exponent_nonneg_of_coefficient_eq_anchor
    {u : Fin n → ℝ} {κ : ℝ} {T : ℕ → ℝ}
    (hu : ∀ i, 0 ≤ u i) (hs : ∀ k ≤ n, 0 ≤ remainingValue u κ k)
    (hκ : 0 < κ) (hT0 : T 0 = 0) (hT : ∀ k, 0 < k → k ≤ n → 2 * κ ≤ T k)
    (β : Fin n → ℤ) (hmem : MeetsLevel u κ T (fun i => β i + 1) 0)
    (hsmall : κ + ∑ i, (β i : ℝ) * u i < 2 * κ) : ∀ i, 0 ≤ β i + 1 := by
  have hm : MeetsLevel u κ T (fun i => β i + 1) (κ - κ) := by simpa using hmem
  have hz := endpoint_quotient_zero_level hu hs hT0 hT β hm hsmall
  simp only [sub_self] at hz
  exact exponent_nonneg_of_zero_coefficient_level u hκ (fun i => β i + 1) hz

end HereditaryAtomicity.DVRBase
