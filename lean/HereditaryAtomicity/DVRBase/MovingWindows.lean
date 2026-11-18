import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Int.Interval
import Mathlib.Tactic

/-!
# Tail-corrected exponent windows

A Lean index i corresponds to variable i+1. Thus poleTail β k includes every exponent
whose index is at least k.
-/

namespace HereditaryAtomicity.DVRBase

open scoped BigOperators

/-- The nonnegative largest pole among the coordinates at or after a cut. -/
def poleTail {N : ℕ} (β : Fin N → ℤ) (k : ℕ) : ℤ :=
  ((Finset.univ.filter fun i : Fin N => k ≤ i.val).sup fun i => (-β i).toNat : ℕ)

theorem poleTail_nonneg {N : ℕ} (β : Fin N → ℤ) (k : ℕ) :
    0 ≤ poleTail β k := Int.natCast_nonneg _

theorem neg_le_poleTail {N : ℕ} (β : Fin N → ℤ) {k : ℕ}
    (i : Fin N) (hi : k ≤ i.val) : -β i ≤ poleTail β k := by
  have h := Finset.le_sup (s := Finset.univ.filter fun j : Fin N => k ≤ j.val)
    (f := fun j : Fin N => (-β j).toNat)
    (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩)
  have hc : ((-β i).toNat : ℤ) ≤ poleTail β k := by
    unfold poleTail
    exact_mod_cast h
  omega

theorem poleTail_le_iff {N : ℕ} (β : Fin N → ℤ) (k : ℕ) (b : ℤ) :
    poleTail β k ≤ b ↔ 0 ≤ b ∧ ∀ i : Fin N, k ≤ i.val → -β i ≤ b := by
  constructor
  · intro h
    exact ⟨(poleTail_nonneg β k).trans h, fun i hi => (neg_le_poleTail β i hi).trans h⟩
  · rintro ⟨hb, h⟩
    have hnat : (Finset.univ.filter fun i : Fin N => k ≤ i.val).sup
        (fun i => (-β i).toNat) ≤ b.toNat := by
      apply Finset.sup_le
      intro i hi
      exact Int.toNat_le_toNat (h i (Finset.mem_filter.mp hi).2)
    have hcast : poleTail β k ≤ (b.toNat : ℤ) := by
      unfold poleTail
      exact_mod_cast hnat
    simpa [Int.toNat_of_nonneg hb] using hcast

theorem poleTail_antitone {N : ℕ} (β : Fin N → ℤ) : Antitone (poleTail β) := by
  intro k l hkl
  exact (poleTail_le_iff β l _).mpr
    ⟨poleTail_nonneg β k, fun i hi => neg_le_poleTail β i (hkl.trans hi)⟩

@[simp] theorem poleTail_of_le {N : ℕ} (β : Fin N → ℤ) {k : ℕ} (hk : N ≤ k) :
    poleTail β k = 0 := by
  apply le_antisymm _ (poleTail_nonneg β k)
  apply (poleTail_le_iff β k 0).mpr
  refine ⟨le_rfl, fun i hi => ?_⟩
  omega

/-- Translate a prefix by the pole order of the discarded suffix. -/
def shiftedPrefix {N l : ℕ} (h : l ≤ N) (β : Fin N → ℤ) : Fin l → ℤ :=
  fun i => β (Fin.castLE h i) + poleTail β l

/-- Tail pole orders transform exactly under the corrected prefix translation. -/
theorem poleTail_shiftedPrefix {N l : ℕ} (h : l ≤ N) (β : Fin N → ℤ)
    {k : ℕ} (hk : k ≤ l) :
    poleTail β k = poleTail β l + poleTail (shiftedPrefix h β) k := by
  have hd := poleTail_nonneg β l
  have hg := poleTail_nonneg (shiftedPrefix h β) k
  apply le_antisymm
  · apply (poleTail_le_iff β k _).mpr
    refine ⟨add_nonneg hd hg, ?_⟩
    intro i hi
    by_cases hil : i.val < l
    · let j : Fin l := ⟨i.val, hil⟩
      have hj := neg_le_poleTail (shiftedPrefix h β) j hi
      have he : Fin.castLE h j = i := Fin.ext rfl
      simp only [shiftedPrefix, he] at hj
      omega
    · have ht := neg_le_poleTail β i (by omega : l ≤ i.val)
      omega
  · have hdk := poleTail_antitone β hk
    have hbound : poleTail (shiftedPrefix h β) k ≤ poleTail β k - poleTail β l := by
      apply (poleTail_le_iff (shiftedPrefix h β) k _).mpr
      refine ⟨sub_nonneg.mpr hdk, ?_⟩
      intro i hi
      have ht := neg_le_poleTail β (Fin.castLE h i) hi
      simp only [shiftedPrefix]
      omega
    omega

/-- A corrected digit absorbs exactly the poles strictly above its coordinate. -/
def correctedDigit {N : ℕ} (β : Fin N → ℤ) (i : Fin N) : ℤ :=
  β i + poleTail β (i.val + 1)

theorem correctedDigit_shiftedPrefix {N l : ℕ} (h : l ≤ N)
    (β : Fin N → ℤ) (i : Fin l) :
    correctedDigit (shiftedPrefix h β) i = correctedDigit β (Fin.castLE h i) := by
  have hp := poleTail_shiftedPrefix h β (k := i.val + 1) (by omega)
  change β (Fin.castLE h i) + poleTail β l +
      poleTail (shiftedPrefix h β) (i.val + 1) =
    β (Fin.castLE h i) + poleTail β (i.val + 1)
  rw [hp]
  omega

/-- The degree-sized integer interval centered at zero, with the upper endpoint omitted. -/
def digitInterval (d : ℕ) : Set ℤ :=
  Set.Ico (-(d / 2 : ℕ) : ℤ) ((d : ℤ) - (d / 2 : ℕ))

/-- An exponent lies in the moving window if all its corrected digits do. -/
def IsWindowExponent {N : ℕ} (D : Fin N → ℕ) (β : Fin N → ℤ) : Prop :=
  ∀ i, correctedDigit β i ∈ digitInterval (D i)

/-- The literal finite-dimensional exponent window. -/
abbrev WindowExponent {N : ℕ} (D : Fin N → ℕ) :=
  {β : Fin N → ℤ // IsWindowExponent D β}

theorem isWindowExponent_shiftedPrefix {N l : ℕ} (h : l ≤ N)
    (D : Fin N → ℕ) (β : Fin N → ℤ) :
    IsWindowExponent (fun i => D (Fin.castLE h i)) (shiftedPrefix h β) ↔
      ∀ i : Fin l, correctedDigit β (Fin.castLE h i) ∈
        digitInterval (D (Fin.castLE h i)) := by
  simp only [IsWindowExponent, correctedDigit_shiftedPrefix]

/-- Every uncorrected coordinate is strictly below its degree. -/
theorem windowExponent_lt_degree {N : ℕ} {D : Fin N → ℕ}
    {β : Fin N → ℤ} (hβ : IsWindowExponent D β) (i : Fin N) : β i < (D i : ℤ) := by
  have hi := (hβ i).2
  have hp := poleTail_nonneg β (i.val + 1)
  change β i + poleTail β (i.val + 1) < (D i : ℤ) - (D i / 2 : ℕ) at hi
  omega

@[simp] theorem poleTail_last {N : ℕ} (β : Fin (N + 1) → ℤ) :
    poleTail β N = max 0 (-β (Fin.last N)) := by
  apply le_antisymm
  · apply (poleTail_le_iff β N _).mpr
    refine ⟨le_max_left _ _, ?_⟩
    intro i hi
    have he : i = Fin.last N := Fin.ext (by simp only [Fin.val_last]; omega)
    simpa only [he] using le_max_right (0 : ℤ) (-β (Fin.last N))
  · exact max_le (poleTail_nonneg β N) (neg_le_poleTail β (Fin.last N) le_rfl)

@[simp] theorem correctedDigit_last {N : ℕ} (β : Fin (N + 1) → ℤ) :
    correctedDigit β (Fin.last N) = β (Fin.last N) := by
  simp [correctedDigit]

/-- Append the last digit, translating all earlier exponents by its pole. -/
def windowSnoc {N : ℕ} (γ : Fin N → ℤ) (j : ℤ) : Fin (N + 1) → ℤ :=
  Fin.snoc (fun i => γ i - max 0 (-j)) j

@[simp] theorem windowSnoc_last {N : ℕ} (γ : Fin N → ℤ) (j : ℤ) :
    windowSnoc γ j (Fin.last N) = j := by simp [windowSnoc]

@[simp] theorem shiftedPrefix_windowSnoc {N : ℕ} (γ : Fin N → ℤ) (j : ℤ) :
    shiftedPrefix (Nat.le_succ N) (windowSnoc γ j) = γ := by
  funext i
  change windowSnoc γ j i.castSucc + poleTail (windowSnoc γ j) N = γ i
  simp [windowSnoc]

@[simp] theorem windowSnoc_shiftedPrefix {N : ℕ} (β : Fin (N + 1) → ℤ) :
    windowSnoc (shiftedPrefix (Nat.le_succ N) β) (β (Fin.last N)) = β := by
  funext i
  cases i using Fin.lastCases with
  | last => simp
  | cast i =>
      simp only [windowSnoc, Fin.snoc_castSucc, shiftedPrefix, poleTail_last]
      exact add_sub_cancel_right _ _

/-- The recursive moving-window test is a prefix window and an independent last digit. -/
theorem isWindowExponent_succ_iff {N : ℕ} (D : Fin (N + 1) → ℕ)
    (β : Fin (N + 1) → ℤ) :
    IsWindowExponent D β ↔
      IsWindowExponent (fun i : Fin N => D i.castSucc)
        (shiftedPrefix (Nat.le_succ N) β) ∧
      β (Fin.last N) ∈ digitInterval (D (Fin.last N)) := by
  rw [IsWindowExponent, Fin.forall_iff_castSucc]
  simp only [correctedDigit_last]
  have he : IsWindowExponent (fun i : Fin N => D i.castSucc)
      (shiftedPrefix (Nat.le_succ N) β) ↔
      ∀ i : Fin N, correctedDigit β i.castSucc ∈ digitInterval (D i.castSucc) :=
    isWindowExponent_shiftedPrefix (Nat.le_succ N) D β
  rw [he, and_comm]

/-- The recursive equivalence between the full exponent window and the shifted prefix
window. -/
def windowSuccEquiv {N : ℕ} (D : Fin (N + 1) → ℕ) :
    WindowExponent D ≃
      WindowExponent (fun i : Fin N => D i.castSucc) ×
        digitInterval (D (Fin.last N)) where
  toFun β :=
    (⟨shiftedPrefix (Nat.le_succ N) β.val,
      ((isWindowExponent_succ_iff D β.val).mp β.property).1⟩,
     ⟨β.val (Fin.last N), ((isWindowExponent_succ_iff D β.val).mp β.property).2⟩)
  invFun p := ⟨windowSnoc p.1.val p.2.val, by
    rw [isWindowExponent_succ_iff]
    simpa using And.intro p.1.property p.2.property⟩
  left_inv β := Subtype.ext (windowSnoc_shiftedPrefix β.val)
  right_inv p := by
    apply Prod.ext
    · exact Subtype.ext (shiftedPrefix_windowSnoc p.1.val p.2.val)
    · exact Subtype.ext (windowSnoc_last p.1.val p.2.val)

/-- The zero-variable window contains exactly the empty exponent vector. -/
def windowZeroEquiv (D : Fin 0 → ℕ) : WindowExponent D ≃ Unit where
  toFun _ := Unit.unit
  invFun _ := ⟨Fin.elim0, fun i => Fin.elim0 i⟩
  left_inv β := Subtype.ext (funext fun i => Fin.elim0 i)
  right_inv p := by cases p; rfl

instance digitInterval_fintype (d : ℕ) : Fintype (digitInterval d) :=
  inferInstanceAs (Fintype (Set.Ico (-(d / 2 : ℕ) : ℤ) ((d : ℤ) - (d / 2 : ℕ))))

instance windowExponent_finite {N : ℕ} (D : Fin N → ℕ) : Finite (WindowExponent D) := by
  induction N with
  | zero => exact Finite.of_equiv Unit (windowZeroEquiv D).symm
  | succ N ih =>
      let := ih (fun i : Fin N => D i.castSucc)
      exact Finite.of_equiv
        (WindowExponent (fun i : Fin N => D i.castSucc) × digitInterval (D (Fin.last N)))
        (windowSuccEquiv D).symm

@[simp] theorem natCard_digitInterval (d : ℕ) : Nat.card (digitInterval d) = d := by
  rw [Nat.card_eq_fintype_card]
  change Fintype.card (Set.Ico (-(d / 2 : ℕ) : ℤ) ((d : ℤ) - (d / 2 : ℕ))) = d
  simp

/-- The moving window has exactly the product of the tower degrees many exponents. -/
theorem natCard_windowExponent {N : ℕ} (D : Fin N → ℕ) :
    Nat.card (WindowExponent D) = ∏ i : Fin N, D i := by
  induction N with
  | zero =>
      rw [Nat.card_congr (windowZeroEquiv D)]
      simp
  | succ N ih =>
      rw [Nat.card_congr (windowSuccEquiv D), Nat.card_prod, natCard_digitInterval, ih,
        Fin.prod_univ_castSucc]

/-- A tail pole depends only on coordinates on that tail. -/
theorem poleTail_eq_of_tail_eq {N : ℕ} {β γ : Fin N → ℤ} {k : ℕ}
    (h : ∀ i : Fin N, k ≤ i.val → β i = γ i) : poleTail β k = poleTail γ k := by
  apply le_antisymm
  · apply (poleTail_le_iff β k _).mpr
    refine ⟨poleTail_nonneg γ k, fun i hi => ?_⟩
    rw [h i hi]
    exact neg_le_poleTail γ i hi
  · apply (poleTail_le_iff γ k _).mpr
    refine ⟨poleTail_nonneg β k, fun i hi => ?_⟩
    rw [← h i hi]
    exact neg_le_poleTail β i hi

/-- If the suffix already passes its windows, the full window test is exactly
the window test on the corrected prefix. -/
theorem isWindowExponent_iff_shiftedPrefix {N l : ℕ} (h : l ≤ N)
    (D : Fin N → ℕ) (β : Fin N → ℤ)
    (htail : ∀ i : Fin N, l ≤ i.val → correctedDigit β i ∈ digitInterval (D i)) :
    IsWindowExponent D β ↔
      IsWindowExponent (fun i => D (Fin.castLE h i)) (shiftedPrefix h β) := by
  rw [isWindowExponent_shiftedPrefix]
  constructor
  · exact fun hβ i => hβ (Fin.castLE h i)
  · intro hprefix i
    by_cases hil : i.val < l
    · let j : Fin l := ⟨i.val, hil⟩
      have he : Fin.castLE h j = i := Fin.ext rfl
      simpa only [he] using hprefix j
    · exact htail i (by omega)

/-- Insert a corrected prefix, undoing its common tail-pole translation. -/
def splicePrefix {N l : ℕ} (_h : l ≤ N) (β : Fin N → ℤ)
    (γ : Fin l → ℤ) : Fin N → ℤ :=
  fun i => if hi : i.val < l then γ ⟨i.val, hi⟩ - poleTail β l else β i

@[simp] theorem splicePrefix_tail {N l : ℕ} (h : l ≤ N) (β : Fin N → ℤ)
    (γ : Fin l → ℤ) (i : Fin N) (hi : l ≤ i.val) : splicePrefix h β γ i = β i := by
  simp only [splicePrefix, dite_eq_right (by omega : ¬ i.val < l)]

@[simp] theorem poleTail_splicePrefix {N l : ℕ} (h : l ≤ N) (β : Fin N → ℤ)
    (γ : Fin l → ℤ) {k : ℕ} (hk : l ≤ k) :
    poleTail (splicePrefix h β γ) k = poleTail β k :=
  poleTail_eq_of_tail_eq fun i hi => splicePrefix_tail h β γ i (hk.trans hi)

@[simp] theorem shiftedPrefix_splicePrefix {N l : ℕ} (h : l ≤ N)
    (β : Fin N → ℤ) (γ : Fin l → ℤ) :
    shiftedPrefix h (splicePrefix h β γ) = γ := by
  funext i
  change splicePrefix h β γ (Fin.castLE h i) +
    poleTail (splicePrefix h β γ) l = γ i
  rw [poleTail_splicePrefix h β γ le_rfl]
  simp only [splicePrefix, Fin.val_castLE, dite_eq_left i.isLt]
  exact sub_add_cancel _ _

@[simp] theorem splicePrefix_shiftedPrefix {N l : ℕ} (h : l ≤ N)
    (β : Fin N → ℤ) : splicePrefix h β (shiftedPrefix h β) = β := by
  funext i
  by_cases hi : i.val < l
  · simp only [splicePrefix, dite_eq_left hi, shiftedPrefix]
    exact add_sub_cancel_right _ _
  · exact splicePrefix_tail h β _ i (by omega)

theorem correctedDigit_splicePrefix_tail {N l : ℕ} (h : l ≤ N)
    (β : Fin N → ℤ) (γ : Fin l → ℤ) (i : Fin N) (hi : l ≤ i.val) :
    correctedDigit (splicePrefix h β γ) i = correctedDigit β i := by
  unfold correctedDigit
  rw [splicePrefix_tail h β γ i hi, poleTail_splicePrefix h β γ (by omega)]

/-- Replace the prefix by a smaller-window exponent and preserve the valid suffix. -/
theorem isWindowExponent_splicePrefix {N l : ℕ} (h : l ≤ N)
    (D : Fin N → ℕ) (β : Fin N → ℤ) (γ : Fin l → ℤ)
    (htail : ∀ i : Fin N, l ≤ i.val → correctedDigit β i ∈ digitInterval (D i))
    (hγ : IsWindowExponent (fun i => D (Fin.castLE h i)) γ) :
    IsWindowExponent D (splicePrefix h β γ) := by
  apply (isWindowExponent_iff_shiftedPrefix h D (splicePrefix h β γ) ?_).mpr
  · simpa only [shiftedPrefix_splicePrefix] using hγ
  · intro i hi
    rw [correctedDigit_splicePrefix_tail h β γ i hi]
    exact htail i hi

/-- Translate the centered integer interval onto the ordinary degree-sized index. -/
def digitIntervalEquivFin (d : ℕ) : digitInterval d ≃ Fin d where
  toFun j := ⟨(j.val + (d / 2 : ℕ)).toNat, by
    have h0 := j.property.1
    have h1 := j.property.2
    change -(d / 2 : ℕ) ≤ j.val at h0
    change j.val < (d : ℤ) - (d / 2 : ℕ) at h1
    omega⟩
  invFun i := ⟨(i.val : ℤ) - (d / 2 : ℕ), by
    change -(d / 2 : ℕ) ≤ (i.val : ℤ) - (d / 2 : ℕ) ∧
      (i.val : ℤ) - (d / 2 : ℕ) < (d : ℤ) - (d / 2 : ℕ)
    constructor <;> omega⟩
  left_inv j := by
    apply Subtype.ext
    change (((j.val + (d / 2 : ℕ)).toNat : ℤ) - (d / 2 : ℕ)) = j.val
    have h0 := j.property.1
    change -(d / 2 : ℕ) ≤ j.val at h0
    omega
  right_inv i := by
    apply Fin.ext
    change (((i.val : ℤ) - (d / 2 : ℕ) + (d / 2 : ℕ)).toNat) = i.val
    omega

@[simp] theorem digitIntervalEquivFin_symm_val (d : ℕ) (i : Fin d) :
    ((digitIntervalEquivFin d).symm i).val = (i.val : ℤ) - (d / 2 : ℕ) := rfl

theorem digitIntervalEquivFin_val (d : ℕ) (j : digitInterval d) :
    ((digitIntervalEquivFin d j).val : ℤ) = j.val + (d / 2 : ℕ) := by
  change (((j.val + (d / 2 : ℕ)).toNat : ℤ)) = j.val + (d / 2 : ℕ)
  have h0 := j.property.1
  change -(d / 2 : ℕ) ≤ j.val at h0
  omega

end HereditaryAtomicity.DVRBase
