import HereditaryAtomicity.DVRBase.ModelOrders

/-!
# Numerical estimates for the moving-window kernel argument

The numerical kernel estimate counts the variable, endpoint, and first-threshold
generators of a product term. The level at which to test the bound may exceed the
first failed window.
-/

namespace HereditaryAtomicity.DVRBase

open scoped BigOperators

/-- A failed corrected digit supplies either a large endpoint count or a large
sum of variable and first-dead-generator counts. -/
theorem kernel_failed_digit_counts (D a b m : ℕ) (β δ ν : ℤ)
    (hβ : β = (a : ℤ) - b + m) (hδ : δ ≤ b) (hν : ν ≤ δ)
    (hfail : β + δ ∉ digitInterval D) :
    ((D / 2 : ℕ) : ℤ) + 1 ≤ (b : ℤ) - ν ∨
      (D : ℤ) - (D / 2 : ℕ) ≤ (a : ℤ) + m := by
  simp only [digitInterval, Set.mem_Ico, not_and_or, not_le, not_lt] at hfail
  rcases hfail with h | h
  · left
    omega
  · right
    omega

/-- The scalar estimate from the two failed-window cases, before the chosen
degree-growth inequality is applied. A, B, Q are the actual nonnegative
variable, endpoint and first-dead-generator contributions at the check cut. -/
theorem kernel_failed_window_bound
    (D a b m : ℕ) (β δ ν : ℤ) (κ u A B Q φ Tk Tl : ℝ)
    (hκ : 1 ≤ κ) (hu : 0 ≤ u) (huκ : u ≤ κ)
    (hβ : β = (a : ℤ) - b + m) (hδ : δ ≤ b) (hν : ν ≤ δ)
    (hfail : β + δ ∉ digitInterval D)
    (hA : (a : ℝ) * u ≤ A) (hB0 : 0 ≤ B) (hB : (b : ℝ) - (ν : ℝ) ≤ B)
    (hQ : Tk - Tl + (2 / 3 : ℝ) * (m : ℝ) * u ≤ Q)
    (hφ : A + B + Q ≤ φ) :
    Tk - Tl + (D : ℝ) * u / (3 * κ) ≤ φ := by
  have hκ0 : 0 < κ := lt_of_lt_of_le zero_lt_one hκ
  have hden : 0 < 3 * κ := mul_pos (by norm_num) hκ0
  have hD : (0 : ℝ) ≤ D := Nat.cast_nonneg D
  have ha : (0 : ℝ) ≤ a := Nat.cast_nonneg a
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hA0 : 0 ≤ A := (mul_nonneg ha hu).trans hA
  have hQ0 : Tk - Tl ≤ Q := by nlinarith only [hQ, mul_nonneg hm hu]
  suffices h : (D : ℝ) * u / (3 * κ) ≤ φ - (Tk - Tl) by linarith
  apply (div_le_iff₀ hden).mpr
  rcases kernel_failed_digit_counts D a b m β δ ν hβ hδ hν hfail with hlo | hhi
  · have hlo' : ((D / 2 : ℕ) : ℝ) + 1 ≤ (b : ℝ) - (ν : ℝ) := by
      have hcast : ((((D / 2 : ℕ) : ℤ) + 1 : ℤ) : ℝ) ≤ (((b : ℤ) - ν : ℤ) : ℝ) :=
        Int.cast_le.mpr hlo
      simpa only [Int.cast_add, Int.cast_one, Int.cast_natCast, Int.cast_sub] using hcast
    have hfloor : (D : ℝ) < 2 * (((D / 2 : ℕ) : ℝ) + 1) := by
      exact_mod_cast (show D < 2 * (D / 2 + 1) by omega)
    have hhalf : (D : ℝ) / 2 ≤ φ - (Tk - Tl) := by linarith
    have hmul := mul_le_mul_of_nonneg_right hhalf hden.le
    have hu' := mul_le_mul_of_nonneg_left huκ hD
    nlinarith only [hmul, hu', mul_nonneg hD hκ0.le]
  · have hhi' : (D : ℝ) - ((D / 2 : ℕ) : ℝ) ≤ (a : ℝ) + m := by exact_mod_cast hhi
    have hfloor : 2 * ((D / 2 : ℕ) : ℝ) ≤ (D : ℝ) := by
      exact_mod_cast (show 2 * (D / 2) ≤ D by omega)
    have hcounts : (D : ℝ) / 2 ≤ (a : ℝ) + m := by linarith
    have hmul := mul_le_mul_of_nonneg_right hcounts hu
    have hthird : (D : ℝ) * u / 3 ≤ φ - (Tk - Tl) := by
      nlinarith only [hA, hB0, hQ, hφ, hmul, mul_nonneg ha hu]
    have hdiff : 0 ≤ φ - (Tk - Tl) :=
      (div_nonneg (mul_nonneg hD hu) (by norm_num : (0 : ℝ) ≤ 3)).trans hthird
    have hκmul := mul_le_mul_of_nonneg_right hκ hdiff
    nlinarith only [hthird, hκmul]

/-- H3 upgrades the failed-window estimate to the exact threshold used by X. -/
theorem kernel_failed_window_estimate
    (D a b m : ℕ) (β δ ν : ℤ) (κ u A B Q φ Tk Tl Ω : ℝ)
    (hκ : 1 ≤ κ) (hu : 0 ≤ u) (huκ : u ≤ κ)
    (hβ : β = (a : ℤ) - b + m) (hδ : δ ≤ b) (hν : ν ≤ δ)
    (hfail : β + δ ∉ digitInterval D)
    (hA : (a : ℝ) * u ≤ A) (hB0 : 0 ≤ B) (hB : (b : ℝ) - (ν : ℝ) ≤ B)
    (hQ : Tk - Tl + (2 / 3 : ℝ) * (m : ℝ) * u ≤ Q)
    (hφ : A + B + Q ≤ φ)
    (hdegree : 3 * κ * (2 * Tl + Ω) ≤ (D : ℝ) * u) :
    Tk + Tl + Ω ≤ φ := by
  have h := kernel_failed_window_bound D a b m β δ ν κ u A B Q φ Tk Tl
    hκ hu huκ hβ hδ hν hfail hA hB0 hB hQ hφ
  have hden : 0 < 3 * κ := by linarith
  have hdiv : 2 * Tl + Ω ≤ (D : ℝ) * u / (3 * κ) := by
    apply (le_div_iff₀ hden).mpr
    nlinarith only [hdegree]
  linarith

variable {N : ℕ}

/-- Numeric data of one first-dead source generator in a fixed finite level. -/
structure KernelGenerator (u : Fin N → ℝ) (κ : ℝ) (T : ℕ → ℝ) where
  level : ℕ
  level_pos : 0 < level
  level_le : level ≤ N
  coefficientExponent : ℕ
  powers : Fin N → ℕ
  dead : T level + remainingValue u κ level ≤
    partialValue u coefficientExponent (fun i => (powers i : ℤ)) level
  earlier : ∀ k < level,
    partialValue u coefficientExponent (fun i => (powers i : ℤ)) k <
      T k + remainingValue u κ k

namespace KernelGenerator

variable {u : Fin N → ℝ} {κ : ℝ} {T : ℕ → ℝ} (g : KernelGenerator u κ T)

/-- The exponent contributed by this generator at one coordinate. -/
def contribution (i : Fin N) : ℕ := if i.val < g.level then g.powers i + 1 else 0

/-- Its literal additive order, retaining the integral coefficient exponent. -/
def order : ℝ := (g.coefficientExponent : ℝ) - κ +
  prefixSum (fun i => ((g.powers i : ℝ) + 1) * u i) g.level

theorem order_eq_partial_sub_remaining : g.order =
    partialValue u g.coefficientExponent (fun i => (g.powers i : ℤ)) g.level -
      remainingValue u κ g.level := by
  simp [order, partialValue, remainingValue, prefixSum, add_mul, Finset.sum_add_distrib]
  ring

theorem threshold_le_order : T g.level ≤ g.order := by
  rw [order_eq_partial_sub_remaining]
  exact (le_sub_iff_add_le).mpr g.dead

theorem order_nonneg (hT : ∀ k ≤ N, 0 ≤ T k) : 0 ≤ g.order :=
  (hT _ g.level_le).trans g.threshold_le_order

theorem coordinate_le_prefixSum (hu : ∀ i, 0 ≤ u i) (i : Fin N) (hi : i.val < g.level) :
    ((g.powers i : ℝ) + 1) * u i ≤
      prefixSum (fun j => ((g.powers j : ℝ) + 1) * u j) g.level := by
  unfold prefixSum
  apply Finset.single_le_sum (a := i)
  · intro j _
    exact mul_nonneg (by positivity) (hu j)
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩

theorem coordinate_sub_anchor_le_order (hu : ∀ i, 0 ≤ u i)
    (i : Fin N) (hi : i.val < g.level) :
    (g.contribution i : ℝ) * u i - κ ≤ g.order := by
  have hp := g.coordinate_le_prefixSum hu i hi
  have he : (0 : ℝ) ≤ g.coefficientExponent := Nat.cast_nonneg _
  simp only [contribution, ite_eq_left hi, Nat.cast_add, Nat.cast_one, order]
  linarith

/-- Each ordinary generator contributes at least two thirds of its exponent
at the failed coordinate, including generators supported below that coordinate. -/
theorem two_thirds_coordinate_le_order (hu : ∀ i, 0 ≤ u i) (hκ : 0 ≤ κ)
    (hT : ∀ k, 0 < k → k ≤ N → 2 * κ ≤ T k) (i : Fin N) :
    (2 / 3 : ℝ) * (g.contribution i : ℝ) * u i ≤ g.order := by
  have hg : 2 * κ ≤ g.order := (hT _ g.level_pos g.level_le).trans g.threshold_le_order
  by_cases hi : i.val < g.level
  · have hc := g.coordinate_sub_anchor_le_order hu i hi
    linarith
  · simp only [contribution, ite_eq_right hi, Nat.cast_zero, mul_zero, zero_mul]
    linarith

/-- First-deadness above the failed cut controls the exceptional generator's
coordinate contribution using the earlier, still-live partial monomial. -/
theorem coordinate_lt_earlier_threshold_add_anchor (hu : ∀ i, 0 ≤ u i)
    (i : Fin N) (hi : i.val + 1 < g.level) :
    (g.contribution i : ℝ) * u i < T (i.val + 1) + κ := by
  have hearlier := g.earlier (i.val + 1) hi
  have hcoord : (g.powers i : ℝ) * u i ≤
      prefixSum (fun j => (g.powers j : ℝ) * u j) (i.val + 1) := by
    unfold prefixSum
    apply Finset.single_le_sum (a := i)
    · intro j _
      exact mul_nonneg (Nat.cast_nonneg _) (hu j)
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Nat.lt_succ_self _⟩
  have he : (0 : ℝ) ≤ g.coefficientExponent := Nat.cast_nonneg _
  have hp : 0 ≤ prefixSum u i.val := Finset.sum_nonneg (fun j _ => hu j)
  have hs := remainingValue_succ u κ i.isLt
  have hsle : remainingValue u κ i.val ≤ κ := sub_le_self _ hp
  simp only [partialValue, Int.cast_natCast] at hearlier
  have hic : i.val < g.level := lt_trans (Nat.lt_succ_self _) hi
  simp only [contribution, ite_eq_left hic, Nat.cast_add, Nat.cast_one]
  nlinarith

/-- The generator at the larger check cut also pays the threshold difference.
This is the part of X that would be lost by replacing the check cut with l. -/
theorem offset_two_thirds_coordinate_le_order (hu : ∀ i, 0 ≤ u i)
    (hT : ∀ k, 0 < k → k ≤ N → 2 * κ ≤ T k)
    (i : Fin N) (hi : i.val + 1 < g.level) :
    T g.level - T (i.val + 1) + (2 / 3 : ℝ) * (g.contribution i : ℝ) * u i ≤ g.order := by
  have hc := g.coordinate_lt_earlier_threshold_add_anchor hu i hi
  have ht := hT (i.val + 1) (Nat.succ_pos _) i.isLt
  have hg := g.threshold_le_order
  linarith

end KernelGenerator

/-- The actual check cut is the maximum of the failed cut and all generator levels. -/
def kernelCheckCut {ι : Type*} [Fintype ι] {u : Fin N → ℝ} {κ : ℝ} {T : ℕ → ℝ}
    (l : ℕ) (g : ι → KernelGenerator u κ T) : ℕ :=
  max l (Finset.univ.sup fun r => (g r).level)

theorem kernelCheckCut_ge {ι : Type*} [Fintype ι] {u : Fin N → ℝ} {κ : ℝ} {T : ℕ → ℝ}
    (l : ℕ) (g : ι → KernelGenerator u κ T) : l ≤ kernelCheckCut l g := le_max_left _ _

theorem kernelCheckCut_generator_le {ι : Type*} [Fintype ι]
    {u : Fin N → ℝ} {κ : ℝ} {T : ℕ → ℝ}
    (l : ℕ) (g : ι → KernelGenerator u κ T) (r : ι) :
    (g r).level ≤ kernelCheckCut l g :=
  (Finset.le_sup (f := fun r => (g r).level) (Finset.mem_univ r)).trans (le_max_right _ _)

theorem kernelCheckCut_le {ι : Type*} [Fintype ι] {u : Fin N → ℝ} {κ : ℝ} {T : ℕ → ℝ}
    {l : ℕ} (hl : l ≤ N) (g : ι → KernelGenerator u κ T) : kernelCheckCut l g ≤ N := by
  apply max_le hl
  exact Finset.sup_le fun r _ => (g r).level_le

theorem exists_generator_at_kernelCheckCut {ι : Type*} [Fintype ι]
    {u : Fin N → ℝ} {κ : ℝ} {T : ℕ → ℝ}
    (l : ℕ) (g : ι → KernelGenerator u κ T) (hlt : l < kernelCheckCut l g) :
    ∃ r, (g r).level = kernelCheckCut l g := by
  classical
  have hs : l < Finset.univ.sup (fun r => (g r).level) := by
    simpa only [kernelCheckCut, lt_max_iff, lt_self_iff_false, false_or] using hlt
  obtain ⟨r, hr, _⟩ := Finset.lt_sup_iff.mp hs
  have hne : (Finset.univ : Finset ι).Nonempty := ⟨r, hr⟩
  obtain ⟨s, _, hsup⟩ := Finset.exists_mem_eq_sup Finset.univ hne (fun r => (g r).level)
  refine ⟨s, ?_⟩
  unfold kernelCheckCut
  rw [max_eq_right hs.le, hsup]

/-- Summing the generator estimates gives the exact Q-contribution bound,
with an additional threshold difference when the check cut is larger. -/
theorem kernel_generator_sum_bound {ι : Type*} [Fintype ι]
    {u : Fin N → ℝ} {κ : ℝ} {T : ℕ → ℝ}
    (hu : ∀ i, 0 ≤ u i) (hκ : 0 ≤ κ)
    (hT : ∀ k, 0 < k → k ≤ N → 2 * κ ≤ T k)
    (g : ι → KernelGenerator u κ T) (i : Fin N) :
    T (kernelCheckCut (i.val + 1) g) - T (i.val + 1) +
      (2 / 3 : ℝ) * (∑ r, ((g r).contribution i : ℝ)) * u i ≤ ∑ r, (g r).order := by
  classical
  let k := kernelCheckCut (i.val + 1) g
  let c : ι → ℝ := fun r => (2 / 3 : ℝ) * ((g r).contribution i : ℝ) * u i
  have hbase : ∀ r, c r ≤ (g r).order :=
    fun r => (g r).two_thirds_coordinate_le_order hu hκ hT i
  have hsum : ∑ r, c r = (2 / 3 : ℝ) * (∑ r, ((g r).contribution i : ℝ)) * u i := by
    simp [c, Finset.mul_sum, Finset.sum_mul]
  by_cases heq : k = i.val + 1
  · have h := Finset.sum_le_sum (fun r (_ : r ∈ Finset.univ) => hbase r)
    simpa only [k, heq, sub_self, zero_add, hsum] using h
  · have hlt : i.val + 1 < k := lt_of_le_of_ne (kernelCheckCut_ge _ _) (Ne.symm heq)
    obtain ⟨r, hr⟩ := exists_generator_at_kernelCheckCut (i.val + 1) g hlt
    have hrlt : i.val + 1 < (g r).level := by simpa only [hr] using hlt
    have hspecial := (g r).offset_two_thirds_coordinate_le_order hu hT i hrlt
    have hsingle : (g r).order - c r ≤ ∑ s, ((g s).order - c s) :=
      Finset.single_le_sum (fun s _ => sub_nonneg.mpr (hbase s)) (Finset.mem_univ r)
    rw [Finset.sum_sub_distrib, hsum] at hsingle
    change T (g r).level - T (i.val + 1) + c r ≤ (g r).order at hspecial
    rw [hr] at hspecial
    linarith

/-- Tail count of endpoint generators, with coordinate j counting every Z_i
whose exponent vector includes that coordinate. -/
def kernelEndpointTail (b : Fin N → ℕ) (k : ℕ) : ℕ :=
  ∑ i ∈ Finset.univ.filter (fun i : Fin N => k ≤ i.val), b i

@[simp] theorem kernelEndpointTail_zero (b : Fin N → ℕ) :
    kernelEndpointTail b 0 = ∑ i, b i := by simp [kernelEndpointTail]

theorem kernelEndpointTail_antitone (b : Fin N → ℕ) : Antitone (kernelEndpointTail b) := by
  intro k l hkl
  unfold kernelEndpointTail
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hkl.trans (Finset.mem_filter.mp hi).2⟩
  · intros
    exact Nat.zero_le _

theorem kernelEndpointTail_le_total (b : Fin N → ℕ) (k : ℕ) :
    kernelEndpointTail b k ≤ ∑ i, b i := by
  simpa using kernelEndpointTail_antitone b (Nat.zero_le k)

theorem kernelEndpointTail_step (b : Fin N → ℕ) {k : ℕ} (hk : k < N) :
    kernelEndpointTail b k = b ⟨k, hk⟩ + kernelEndpointTail b (k + 1) := by
  have hset : (Finset.univ.filter fun i : Fin N => k ≤ i.val) =
      insert ⟨k, hk⟩ (Finset.univ.filter fun i : Fin N => k + 1 ≤ i.val) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
    omega
  have hnot : (⟨k, hk⟩ : Fin N) ∉ Finset.univ.filter (fun i : Fin N => k + 1 ≤ i.val) := by simp
  simp only [kernelEndpointTail, hset, Finset.sum_insert hnot]

theorem kernelEndpoint_count_split (b : Fin N → ℕ) (k : ℕ) :
    (∑ i ∈ Finset.univ.filter (fun i : Fin N => i.val < k), b i) +
      kernelEndpointTail b k = ∑ i, b i := by
  unfold kernelEndpointTail
  rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i.val < k
  · simp [hi, not_le.mpr hi]
  · simp [hi, Nat.le_of_not_gt hi]

/-- The exact endpoint-count identity in equation (2) of Lemma X, before
subtracting the pole correction. -/
theorem kernelEndpoint_partial_identity (u : Fin N → ℝ) (κ : ℝ) (b : Fin N → ℕ)
    {k : ℕ} (hk : k ≤ N) :
    κ * (∑ i, (b i : ℝ)) -
        prefixSum (fun i => (kernelEndpointTail b i.val : ℝ) * u i) k =
      prefixSum (fun i => (b i : ℝ) * remainingValue u κ (i.val + 1)) k +
        (kernelEndpointTail b k : ℝ) * remainingValue u κ k := by
  induction k with
  | zero => simp [Nat.cast_sum, mul_comm]
  | succ k ih =>
      have hkn : k < N := by omega
      have hi := ih (by omega : k ≤ N)
      have hb : (kernelEndpointTail b k : ℝ) =
          (b ⟨k, hkn⟩ : ℝ) + (kernelEndpointTail b (k + 1) : ℝ) := by
        exact_mod_cast kernelEndpointTail_step b hkn
      have hs := remainingValue_succ u κ hkn
      rw [prefixSum_succ _ hkn, prefixSum_succ _ hkn]
      change κ * (∑ i, (b i : ℝ)) -
          (prefixSum (fun i => (kernelEndpointTail b i.val : ℝ) * u i) k +
            (kernelEndpointTail b k : ℝ) * u ⟨k, hkn⟩) = _
      rw [sub_add_eq_sub_sub, hi, hs, hb]
      ring

/-- The total positive-generator count at one coordinate. -/
def kernelGeneratorCount {ι : Type*} [Fintype ι] {u : Fin N → ℝ} {κ : ℝ} {T : ℕ → ℝ}
    (g : ι → KernelGenerator u κ T) (i : Fin N) : ℕ := ∑ r, (g r).contribution i

/-- Literal exponent of a product of variable, endpoint and first-dead generators. -/
def kernelProductExponent {ι : Type*} [Fintype ι] {u : Fin N → ℝ} {κ : ℝ} {T : ℕ → ℝ}
    (a b : Fin N → ℕ) (g : ι → KernelGenerator u κ T) (i : Fin N) : ℤ :=
  (a i : ℤ) - (kernelEndpointTail b i.val : ℤ) + (kernelGeneratorCount g i : ℤ)

theorem kernelProductExponent_pole_le {ι : Type*} [Fintype ι]
    {u : Fin N → ℝ} {κ : ℝ} {T : ℕ → ℝ}
    (a b : Fin N → ℕ) (g : ι → KernelGenerator u κ T) (k : ℕ) :
    poleTail (kernelProductExponent a b g) k ≤ (kernelEndpointTail b k : ℤ) := by
  apply (poleTail_le_iff _ k _).mpr
  refine ⟨Int.natCast_nonneg _, ?_⟩
  intro i hi
  have htail : (kernelEndpointTail b i.val : ℤ) ≤ (kernelEndpointTail b k : ℤ) := by
    exact_mod_cast kernelEndpointTail_antitone b hi
  dsimp [kernelProductExponent]
  omega

theorem KernelGenerator.prefix_contribution {u : Fin N → ℝ} {κ : ℝ} {T : ℕ → ℝ}
    (g : KernelGenerator u κ T) {k : ℕ} (hk : g.level ≤ k) :
    prefixSum (fun i => (g.contribution i : ℝ) * u i) k =
      prefixSum (fun i => ((g.powers i : ℝ) + 1) * u i) g.level := by
  unfold prefixSum
  rw [Finset.sum_filter, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i.val < g.level
  · have hik : i.val < k := hi.trans_le hk
    simp [KernelGenerator.contribution, hi, hik]
  · simp [KernelGenerator.contribution, hi]

theorem kernelGeneratorCount_prefix {ι : Type*} [Fintype ι]
    {u : Fin N → ℝ} {κ : ℝ} {T : ℕ → ℝ}
    (g : ι → KernelGenerator u κ T) (k : ℕ) :
    prefixSum (fun i => (kernelGeneratorCount g i : ℝ) * u i) k =
      ∑ r, prefixSum (fun i => ((g r).contribution i : ℝ) * u i) k := by
  unfold prefixSum kernelGeneratorCount
  simp only [Nat.cast_sum, Finset.sum_mul]
  rw [Finset.sum_comm]

/-- The coefficient order before collection of a literal product term. -/
def kernelProductCoefficient {ι : Type*} [Fintype ι] {u : Fin N → ℝ} {κ : ℝ} {T : ℕ → ℝ}
    (e : ℝ) (b : Fin N → ℕ) (g : ι → KernelGenerator u κ T) : ℝ :=
  e + κ * (∑ i, (b i : ℝ)) + (∑ r, (((g r).coefficientExponent : ℝ) - κ))

/-- The endpoint contribution after the pole correction at the check cut. -/
def kernelEndpointPart (u : Fin N → ℝ) (κ : ℝ) (b : Fin N → ℕ) (ν : ℤ) (k : ℕ) : ℝ :=
  prefixSum (fun i => (b i : ℝ) * remainingValue u κ (i.val + 1)) k +
    ((kernelEndpointTail b k : ℝ) - (ν : ℝ)) * remainingValue u κ k

/-- Equation (2) of X for literal count data. All first-dead generator lengths
must be at most the check cut; the check cut need not be the failed cut. -/
theorem kernelProductLevel_identity {ι : Type*} [Fintype ι]
    {u : Fin N → ℝ} {κ : ℝ} {T : ℕ → ℝ}
    (e : ℝ) (a b : Fin N → ℕ) (g : ι → KernelGenerator u κ T)
    {k : ℕ} (hk : k ≤ N) (hgk : ∀ r, (g r).level ≤ k) :
    levelValue u κ (kernelProductCoefficient e b g) (kernelProductExponent a b g) k =
      e + prefixSum (fun i => (a i : ℝ) * u i) k +
        kernelEndpointPart u κ b (poleTail (kernelProductExponent a b g) k) k +
        ∑ r, (g r).order := by
  have hβ : prefixSum (fun i => (kernelProductExponent a b g i : ℝ) * u i) k =
      prefixSum (fun i => (a i : ℝ) * u i) k -
      prefixSum (fun i => (kernelEndpointTail b i.val : ℝ) * u i) k +
      prefixSum (fun i => (kernelGeneratorCount g i : ℝ) * u i) k := by
    simp [prefixSum, kernelProductExponent, sub_mul, add_mul,
      Finset.sum_sub_distrib, Finset.sum_add_distrib]
  have hg : (∑ r, (((g r).coefficientExponent : ℝ) - κ)) +
        prefixSum (fun i => (kernelGeneratorCount g i : ℝ) * u i) k =
      ∑ r, (g r).order := by
    rw [kernelGeneratorCount_prefix]
    simp only [KernelGenerator.order, Finset.sum_add_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro r _
    exact (g r).prefix_contribution (hgk r)
  have hb := kernelEndpoint_partial_identity u κ b hk
  simp only [levelValue, partialValue, kernelProductCoefficient, hβ, kernelEndpointPart]
  linarith

/-- Endpoint counts contribute at least the total endpoint count less the
remaining pole order, because every endpoint value is at least one. -/
theorem kernelEndpointPart_lower (u : Fin N → ℝ) (κ : ℝ) (b : Fin N → ℕ)
    (ν : ℤ) {k : ℕ} (hk : k ≤ N)
    (hs : ∀ j ≤ N, 1 ≤ remainingValue u κ j)
    (hν : ν ≤ (kernelEndpointTail b k : ℤ)) :
    (∑ i, (b i : ℝ)) - (ν : ℝ) ≤ kernelEndpointPart u κ b ν k := by
  have hp : prefixSum (fun i => (b i : ℝ)) k ≤
      prefixSum (fun i => (b i : ℝ) * remainingValue u κ (i.val + 1)) k := by
    unfold prefixSum
    apply Finset.sum_le_sum
    intro i _
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (hs (i.val + 1) i.isLt)
      (Nat.cast_nonneg (b i) : (0 : ℝ) ≤ _)
  have hν' : (ν : ℝ) ≤ (kernelEndpointTail b k : ℝ) := by exact_mod_cast hν
  have htail := mul_le_mul_of_nonneg_left (hs k hk) (sub_nonneg.mpr hν')
  have hsplit : prefixSum (fun i => (b i : ℝ)) k + (kernelEndpointTail b k : ℝ) =
      ∑ i, (b i : ℝ) := by
    simpa only [prefixSum, Nat.cast_add, Nat.cast_sum] using
      congrArg (fun z : ℕ => (z : ℝ)) (kernelEndpoint_count_split b k)
  unfold kernelEndpointPart
  linarith

theorem kernelEndpointPart_nonneg (u : Fin N → ℝ) (κ : ℝ) (b : Fin N → ℕ)
    (ν : ℤ) {k : ℕ} (hk : k ≤ N)
    (hs : ∀ j ≤ N, 1 ≤ remainingValue u κ j)
    (hν : ν ≤ (kernelEndpointTail b k : ℤ)) : 0 ≤ kernelEndpointPart u κ b ν k := by
  have ht : (kernelEndpointTail b k : ℝ) ≤ ∑ i, (b i : ℝ) := by
    exact_mod_cast kernelEndpointTail_le_total b k
  have hν' : (ν : ℝ) ≤ (kernelEndpointTail b k : ℝ) := by exact_mod_cast hν
  exact (sub_nonneg.mpr (hν'.trans ht)).trans (kernelEndpointPart_lower u κ b ν hk hs hν)

/-- The full numerical estimate of Lemma X for an actual product term, with
the check cut chosen as the maximum of the failed cut and all generator lengths. -/
theorem kernelProduct_failed_window_estimate {ι : Type*} [Fintype ι]
    {u : Fin N → ℝ} {κ : ℝ} {T : ℕ → ℝ}
    (hu : ∀ j, 0 ≤ u j) (hκ : 1 ≤ κ) (huκ : ∀ j, u j ≤ κ)
    (hs : ∀ k ≤ N, 1 ≤ remainingValue u κ k)
    (hT : ∀ k, 0 < k → k ≤ N → 2 * κ ≤ T k)
    (e : ℝ) (he : 0 ≤ e) (a b : Fin N → ℕ) (g : ι → KernelGenerator u κ T)
    (i : Fin N) (D : ℕ) (Ω : ℝ)
    (hfail : correctedDigit (kernelProductExponent a b g) i ∉ digitInterval D)
    (hdegree : 3 * κ * (2 * T (i.val + 1) + Ω) ≤ (D : ℝ) * u i) :
    T (kernelCheckCut (i.val + 1) g) + T (i.val + 1) + Ω ≤
      levelValue u κ (kernelProductCoefficient e b g) (kernelProductExponent a b g)
        (kernelCheckCut (i.val + 1) g) := by
  let β := kernelProductExponent a b g
  let k := kernelCheckCut (i.val + 1) g
  let δ := poleTail β (i.val + 1)
  let ν := poleTail β k
  let A := prefixSum (fun j => (a j : ℝ) * u j) k
  let B := kernelEndpointPart u κ b ν k
  let Q := ∑ r, (g r).order
  have hk : k ≤ N := kernelCheckCut_le i.isLt g
  have hlk : i.val + 1 ≤ k := kernelCheckCut_ge _ _
  have hνtail : ν ≤ (kernelEndpointTail b k : ℤ) := kernelProductExponent_pole_le a b g k
  have hδ : δ ≤ (kernelEndpointTail b i.val : ℤ) := by
    exact (kernelProductExponent_pole_le a b g (i.val + 1)).trans
      (by exact_mod_cast kernelEndpointTail_antitone b (Nat.le_succ i.val))
  have hν : ν ≤ δ := poleTail_antitone β hlk
  have hA : (a i : ℝ) * u i ≤ A := by
    unfold A prefixSum
    apply Finset.single_le_sum (a := i)
    · intro j _
      exact mul_nonneg (Nat.cast_nonneg _) (hu j)
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Nat.lt_succ_self _).trans_le hlk⟩
  have hB0 : 0 ≤ B := kernelEndpointPart_nonneg u κ b ν hk hs hνtail
  have hB : (kernelEndpointTail b i.val : ℝ) - (ν : ℝ) ≤ B := by
    have ht : (kernelEndpointTail b i.val : ℝ) ≤ ∑ j, (b j : ℝ) := by
      exact_mod_cast kernelEndpointTail_le_total b i.val
    exact (sub_le_sub_right ht _).trans (kernelEndpointPart_lower u κ b ν hk hs hνtail)
  have hQ : T k - T (i.val + 1) + (2 / 3 : ℝ) * (kernelGeneratorCount g i : ℝ) * u i ≤ Q := by
    simpa only [kernelGeneratorCount, Nat.cast_sum] using
      kernel_generator_sum_bound hu (le_trans zero_le_one hκ) hT g i
  have hφ : A + B + Q ≤ levelValue u κ (kernelProductCoefficient e b g) β k := by
    rw [kernelProductLevel_identity e a b g hk (kernelCheckCut_generator_le _ _)]
    change A + B + Q ≤ e + A + B + Q
    linarith
  exact kernel_failed_window_estimate D (a i) (kernelEndpointTail b i.val)
    (kernelGeneratorCount g i) (β i) δ ν κ (u i) A B Q
    (levelValue u κ (kernelProductCoefficient e b g) β k) (T k) (T (i.val + 1)) Ω
    hκ (hu i) (huκ i) rfl hδ hν hfail hA hB0 hB hQ hφ hdegree

/-- The block threshold at the failed cut strictly exceeds the two endpoint
orders lost in the kernel criterion. -/
theorem kernel_threshold_gap (u : Fin N → ℝ) (κ : ℝ) (T : ℕ → ℝ)
    (hu : ∀ i, 0 < u i) (hT : ∀ j, 0 < j → j ≤ N → 2 * κ ≤ T j)
    {l k : ℕ} (hl : 0 < l) (hlk : l ≤ k) (hk : k ≤ N) :
    remainingValue u κ k + remainingValue u κ 1 < T l := by
  have hN : 0 < N := hl.trans_le (hlk.trans hk)
  let i : Fin N := ⟨0, hN⟩
  have hp (j : ℕ) (hj : 0 < j) : u i ≤ prefixSum u j := by
    unfold prefixSum
    apply Finset.single_le_sum (a := i)
    · intro z _
      exact (hu z).le
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩
  have hpk := hp k (hl.trans_le hlk)
  have hp1 := hp 1 Nat.zero_lt_one
  have hi := hu i
  have ht := hT l hl (hlk.trans hk)
  unfold remainingValue
  linarith

/-- The literal numerical criterion after an admissible previous-level
coordinate loss: each resulting term clears the required Z₁J₀ threshold. -/
theorem kernelProduct_after_loss {ι : Type*} [Fintype ι]
    {u : Fin N → ℝ} {κ : ℝ} {T : ℕ → ℝ}
    (hu : ∀ j, 0 < u j) (hκ : 1 ≤ κ) (huκ : ∀ j, u j ≤ κ)
    (hs : ∀ k ≤ N, 1 ≤ remainingValue u κ k)
    (hT : ∀ k, 0 < k → k ≤ N → 2 * κ ≤ T k)
    (e : ℝ) (he : 0 ≤ e) (a b : Fin N → ℕ) (g : ι → KernelGenerator u κ T)
    (i : Fin N) (D : ℕ) (Ω value : ℝ)
    (hfail : correctedDigit (kernelProductExponent a b g) i ∉ digitInterval D)
    (hdegree : 3 * κ * (2 * T (i.val + 1) + Ω) ≤ (D : ℝ) * u i)
    (hloss : levelValue u κ (kernelProductCoefficient e b g) (kernelProductExponent a b g)
        (kernelCheckCut (i.val + 1) g) - Ω ≤ value) :
    T (kernelCheckCut (i.val + 1) g) + remainingValue u κ (kernelCheckCut (i.val + 1) g) +
      remainingValue u κ 1 < value := by
  have hmain := kernelProduct_failed_window_estimate (fun j => (hu j).le) hκ huκ hs hT
    e he a b g i D Ω hfail hdegree
  have hgap := kernel_threshold_gap u κ T hu hT (Nat.succ_pos i.val)
    (kernelCheckCut_ge _ _) (kernelCheckCut_le i.isLt g)
  linarith

theorem kernel_poleTail_antitone_exponent (β γ : Fin N → ℤ)
    (h : ∀ i, β i ≤ γ i) (k : ℕ) : poleTail γ k ≤ poleTail β k := by
  apply (poleTail_le_iff γ k _).mpr
  refine ⟨poleTail_nonneg β k, ?_⟩
  intro i hi
  exact (neg_le_neg (h i)).trans (neg_le_poleTail β i hi)

theorem kernel_prefixSum_first (u : Fin N → ℝ) (i : Fin N) (hi : i.val = 0) :
    prefixSum u 1 = u i := by
  unfold prefixSum
  rw [Finset.sum_eq_single i]
  · intro j hj hji
    have hjval := (Finset.mem_filter.mp hj).2
    have hjeq : j = i := Fin.ext (by omega)
    exact False.elim (hji hjeq)
  · intro h
    exact False.elim (h (Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩))

theorem kernel_prefixSum_single (u : Fin N → ℝ) (i : Fin N)
    {k : ℕ} (hi : i.val < k) :
    prefixSum (fun j => (((Pi.single i (1 : ℤ) : Fin N → ℤ) j : ℤ) : ℝ) * u j) k = u i := by
  classical
  unfold prefixSum
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    simp [Pi.single_eq_of_ne hji]
  · intro h
    exact False.elim (h (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩))

/-- Exponent of the quotient by Z₁Z_N; the constant coefficient order loses 2κ. -/
def kernelCorrectionExponent (β : Fin N → ℤ) (first : Fin N) : Fin N → ℤ :=
  β + (fun _ => 1) + Pi.single first 1

theorem kernelCorrection_partial (u : Fin N → ℝ) (κ e : ℝ) (β : Fin N → ℤ)
    (first : Fin N) (hfirst : first.val = 0) {k : ℕ} (hk : 0 < k) :
    partialValue u (e - 2 * κ) (kernelCorrectionExponent β first) k =
      partialValue u e β k - remainingValue u κ k - remainingValue u κ 1 := by
  classical
  have hs := kernel_prefixSum_single u first (k := k) (by omega)
  have hf := kernel_prefixSum_first u first hfirst
  have hdot : prefixSum (fun j => ((kernelCorrectionExponent β first j : ℤ) : ℝ) * u j) k =
      prefixSum (fun j => (β j : ℝ) * u j) k + prefixSum u k + u first := by
    unfold kernelCorrectionExponent
    simp only [Pi.add_apply, Int.cast_add, Int.cast_one, add_mul, one_mul]
    rw [prefixSum_add, prefixSum_add, hs]
  simp only [partialValue, hdot, remainingValue, hf]
  ring

theorem kernelCorrection_pole_le (β : Fin N → ℤ) (first : Fin N) (k : ℕ) :
    poleTail (kernelCorrectionExponent β first) k ≤ poleTail β k := by
  classical
  apply kernel_poleTail_antitone_exponent
  intro i
  simp only [kernelCorrectionExponent, Pi.add_apply, Pi.single_apply]
  split_ifs <;> omega

/-- The pole correction does not increase under division by Z₁Z_N; hence the
level value loses at most s₁+s_k, exactly as in the criterion of Lemma X. -/
theorem kernelCorrection_level_ge (u : Fin N → ℝ) (κ e : ℝ) (β : Fin N → ℤ)
    (first : Fin N) (hfirst : first.val = 0) {k : ℕ} (hk : 0 < k)
    (hs : 0 ≤ remainingValue u κ k) :
    levelValue u κ e β k - remainingValue u κ k - remainingValue u κ 1 ≤
      levelValue u κ (e - 2 * κ) (kernelCorrectionExponent β first) k := by
  have hd : (poleTail (kernelCorrectionExponent β first) k : ℝ) ≤ (poleTail β k : ℝ) := by
    exact_mod_cast kernelCorrection_pole_le β first k
  have hm := mul_le_mul_of_nonneg_right hd hs
  simp only [levelValue, kernelCorrection_partial u κ e β first hfirst hk]
  linarith

/-- Numerical membership criterion for the quotient by Z₁Z_N. Combined with
Lemma 6.5(b), this gives the actual monomial containment in Z₁J₀. -/
theorem kernelCorrection_meetsLevel (u : Fin N → ℝ) (κ e : ℝ) (T : ℕ → ℝ)
    (β : Fin N → ℤ) (first : Fin N) (hfirst : first.val = 0)
    {k : ℕ} (hk : 0 < k) (hkN : k ≤ N) (hs : 0 ≤ remainingValue u κ k)
    (hcriterion : T k + remainingValue u κ k + remainingValue u κ 1 ≤ levelValue u κ e β k) :
    MeetsLevel u κ T (kernelCorrectionExponent β first) (e - 2 * κ) := by
  refine ⟨k, hkN, ?_⟩
  have h := kernelCorrection_level_ge u κ e β first hfirst hk hs
  linarith

end HereditaryAtomicity.DVRBase
