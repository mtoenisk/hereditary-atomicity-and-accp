import HereditaryAtomicity.DVRBase.Model

/-!
# Disjoint variable shifts and the positive-level model class

Each mask represents a squarefree monomial. Raising the selected exponents by one
reduces the remaining pole order by at most one. For two disjoint masks at least one
preserves a coordinate realizing that order. At positive levels, omission of the first
variable leaves the required weight gap below κ.
-/

namespace HereditaryAtomicity.DVRBase

variable {n : ℕ}

/-- The exponent vector of the squarefree product on a finite variable set. -/
def maskExponent (X : Finset (Fin n)) (i : Fin n) : ℤ :=
  if i ∈ X then 1 else 0

@[simp] theorem maskExponent_of_mem (X : Finset (Fin n)) (i : Fin n) (hi : i ∈ X) :
    maskExponent X i = 1 := by simp [maskExponent, hi]

@[simp] theorem maskExponent_of_not_mem (X : Finset (Fin n)) (i : Fin n) (hi : i ∉ X) :
    maskExponent X i = 0 := by simp [maskExponent, hi]

theorem maskExponent_nonneg (X : Finset (Fin n)) (i : Fin n) :
    0 ≤ maskExponent X i := by
  simp only [maskExponent]
  split_ifs <;> norm_num

theorem maskExponent_le_one (X : Finset (Fin n)) (i : Fin n) :
    maskExponent X i ≤ 1 := by
  simp only [maskExponent]
  split_ifs <;> norm_num

/-- Multiplication by a squarefree variable monomial cannot increase a tail pole. -/
theorem poleTail_add_mask_le (β : Fin n → ℤ) (X : Finset (Fin n)) (k : ℕ) :
    poleTail (β + maskExponent X) k ≤ poleTail β k := by
  apply (poleTail_le_iff _ k _).mpr
  refine ⟨poleTail_nonneg β k, ?_⟩
  intro i hi
  have hb := neg_le_poleTail β i hi
  have hm := maskExponent_nonneg X i
  simp only [Pi.add_apply]
  omega

/-- Multiplication by a squarefree variable monomial reduces a tail pole by at most one. -/
theorem poleTail_le_add_mask_add_one (β : Fin n → ℤ) (X : Finset (Fin n)) (k : ℕ) :
    poleTail β k ≤ poleTail (β + maskExponent X) k + 1 := by
  apply (poleTail_le_iff β k _).mpr
  refine ⟨by have := poleTail_nonneg (β + maskExponent X) k; omega, ?_⟩
  intro i hi
  have hb := neg_le_poleTail (β + maskExponent X) i hi
  have hm := maskExponent_le_one X i
  simp only [Pi.add_apply] at hb
  omega

/-- Two disjoint squarefree shifts cannot both decrease the maximal remaining pole. -/
theorem poleTail_max_add_masks_of_disjoint (β : Fin n → ℤ)
    (L D : Finset (Fin n)) (hLD : Disjoint L D) (k : ℕ) :
    max (poleTail (β + maskExponent L) k) (poleTail (β + maskExponent D) k) =
      poleTail β k := by
  apply le_antisymm
  · exact max_le (poleTail_add_mask_le β L k) (poleTail_add_mask_le β D k)
  · apply (poleTail_le_iff β k _).mpr
    refine ⟨(poleTail_nonneg (β + maskExponent L) k).trans (le_max_left _ _), ?_⟩
    intro i hi
    by_cases hLi : i ∈ L
    · have hDi : i ∉ D := Finset.disjoint_left.mp hLD hLi
      have h := neg_le_poleTail (β + maskExponent D) i hi
      simp only [Pi.add_apply, maskExponent_of_not_mem D i hDi, add_zero] at h
      exact h.trans (le_max_right _ _)
    · have h := neg_le_poleTail (β + maskExponent L) i hi
      simp only [Pi.add_apply, maskExponent_of_not_mem L i hLi, add_zero] at h
      exact h.trans (le_max_left _ _)

end HereditaryAtomicity.DVRBase

namespace HereditaryAtomicity.DVRBase
open scoped BigOperators
variable {n : ℕ}

/-- Indicator multiplication adds exactly the selected prefix weight. -/
theorem partialValue_add_mask (u : Fin n → ℝ) (e : ℝ) (β : Fin n → ℤ)
    (X : Finset (Fin n)) (k : ℕ) :
    partialValue u e (β + maskExponent X) k = partialValue u e β k +
      ∑ i ∈ X.filter (fun i => i.val < k), u i := by
  classical
  have hs : prefixSum (fun i => if i ∈ X then u i else 0) k =
      ∑ i ∈ X.filter (fun i => i.val < k), u i := by
    unfold prefixSum
    rw [← Finset.sum_filter]
    congr 1
    ext i
    simp [and_comm]
  have he : (fun i => (((β + maskExponent X) i : ℤ) : ℝ) * u i) =
      (fun i => (β i : ℝ) * u i + (if i ∈ X then u i else 0)) := by
    funext i
    simp only [Pi.add_apply, maskExponent, Int.cast_add]
    split_ifs <;> push_cast <;> ring
  simp only [partialValue, he, prefixSum_add, hs]
  ring

/-- Omitting the first coordinate leaves a strict gap below κ after adding
any selected prefix to the remaining endpoint order. -/
theorem remainingValue_add_selectedPrefix_lt (P : ModelParameters n)
    (X : Finset (Fin n)) (hn : 0 < n) (hX : (⟨0, hn⟩ : Fin n) ∉ X)
    {k : ℕ} (hk : 0 < k) :
    remainingValue P.weights P.kappa k +
      (∑ i ∈ X.filter (fun i => i.val < k), P.weights i) < P.kappa := by
  classical
  let s := Finset.univ.filter (fun i : Fin n => i.val < k)
  have hfirst : (⟨0, hn⟩ : Fin n) ∈ s := by simp [s, hk]
  have hsub : X.filter (fun i => i.val < k) ⊆ s.erase ⟨0, hn⟩ := by
    intro i hi
    obtain ⟨hiX, hik⟩ := Finset.mem_filter.mp hi
    have hi0 : i ≠ (⟨0, hn⟩ : Fin n) := by
      intro he
      exact hX (he ▸ hiX)
    simp [s, hi0, hik]
  have hle := Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun i _ _ => (P.weights_pos i).le)
  have hsum : (∑ i ∈ s.erase ⟨0, hn⟩, P.weights i) + P.weights ⟨0, hn⟩ =
      prefixSum P.weights k := by
    exact Finset.sum_erase_add s P.weights hfirst
  have hpos := P.weights_pos ⟨0, hn⟩
  unfold remainingValue
  linarith

/-- A positive-cut witness after a mask shift yields a strictly stronger
witness after increasing the original coefficient order by κ. -/
theorem levelValue_add_mask_lt_add_kappa (P : ModelParameters n)
    (β : Fin n → ℤ) (e : ℝ) (X : Finset (Fin n))
    (hn : 0 < n) (hX : (⟨0, hn⟩ : Fin n) ∉ X)
    {k : ℕ} (hk : 0 < k) (hkn : k ≤ n) :
    levelValue P.weights P.kappa e (β + maskExponent X) k <
      levelValue P.weights P.kappa (e + P.kappa) β k := by
  have hdrop : (poleTail β k : ℝ) ≤ (poleTail (β + maskExponent X) k : ℝ) + 1 := by
    exact_mod_cast poleTail_le_add_mask_add_one β X k
  have hmul := mul_le_mul_of_nonneg_right hdrop (P.remaining_pos k hkn).le
  have hgap := remainingValue_add_selectedPrefix_lt P X hn hX hk
  have hcoef : partialValue P.weights (e + P.kappa) β k =
      partialValue P.weights e β k + P.kappa := by
    unfold partialValue
    ring
  simp only [levelValue, partialValue_add_mask, hcoef]
  nlinarith only [hmul, hgap]

/-- Lemma 6.8(b), numerically: disjoint shifts can both meet the ring thresholds
only if the original monomial lies in the ring class or in the κ-shifted
positive-level class. No partition covering assumption is required. -/
theorem meetsLevel_of_disjoint_masks (P : ModelParameters n)
    (β : Fin n → ℤ) (e : ℝ) (L D : Finset (Fin n)) (hLD : Disjoint L D)
    (hn : 0 < n) (hL0 : (⟨0, hn⟩ : Fin n) ∉ L) (hD0 : (⟨0, hn⟩ : Fin n) ∉ D)
    (hL : MeetsLevel P.weights P.kappa P.thresholds (β + maskExponent L) e)
    (hD : MeetsLevel P.weights P.kappa P.thresholds (β + maskExponent D) e) :
    MeetsLevel P.weights P.kappa P.thresholds β e ∨
      ∃ k, 0 < k ∧ k ≤ n ∧ P.thresholds k ≤
        levelValue P.weights P.kappa (e + P.kappa) β k := by
  obtain ⟨k, hkn, hk⟩ := hL
  obtain ⟨l, hln, hl⟩ := hD
  by_cases hk0 : k = 0
  · subst k
    by_cases hl0 : l = 0
    · subst l
      left
      refine ⟨0, Nat.zero_le _, ?_⟩
      have hmax := poleTail_max_add_masks_of_disjoint β L D hLD 0
      rcases le_total (poleTail (β + maskExponent L) 0)
          (poleTail (β + maskExponent D) 0) with hle | hle
      · rw [max_eq_right hle] at hmax
        simpa only [levelValue, partialValue_zero, remainingValue_zero, hmax] using hl
      · rw [max_eq_left hle] at hmax
        simpa only [levelValue, partialValue_zero, remainingValue_zero, hmax] using hk
    · right
      exact ⟨l, Nat.pos_of_ne_zero hl0, hln,
        hl.trans (levelValue_add_mask_lt_add_kappa P β e D hn hD0
          (Nat.pos_of_ne_zero hl0) hln).le⟩
  · right
    exact ⟨k, Nat.pos_of_ne_zero hk0, hkn,
      hk.trans (levelValue_add_mask_lt_add_kappa P β e L hn hL0
        (Nat.pos_of_ne_zero hk0) hkn).le⟩

end HereditaryAtomicity.DVRBase
