import UnconditionalCounterexample.Variations.DyadicEscape

/-!
# Finite blocks for simultaneous dyadic choices

A round can request an arbitrarily large new interval of regular indices and
finitely many auxiliary columns. Emit its auxiliary columns, then all adjacent
columns of that interval, then all balanced columns. A transposition puts a
designated balanced column last so its unit targets can use the other factors
of the split. The round lengths and the designated columns may vary arbitrarily.
-/

namespace UnconditionalCounterexample.DyadicBlocks

open DyadicEscape

/-- Left endpoints of successive disjoint intervals. -/
def boundary (width : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | n+1 => boundary width n + width n

theorem boundary_mono {w : ℕ → ℕ} (hw : ∀ r, 0 < w r) : StrictMono (boundary w) :=
  strictMono_nat_of_lt_succ fun r => Nat.lt_add_of_pos_right (hw r)

private theorem boundary_unbounded {w : ℕ → ℕ} (hw : ∀ r, 0 < w r) (n : ℕ) :
    ∃ r, n < boundary w (r+1) :=
  ⟨n, (Nat.lt_succ_self n).trans_le ((boundary_mono hw).id_le (n+1))⟩

/-- The unique round containing an index. -/
noncomputable def locate {w : ℕ → ℕ} (hw : ∀ r, 0 < w r) (n : ℕ) : ℕ :=
  Nat.find (boundary_unbounded hw n)

theorem locate_bounds {w : ℕ → ℕ} (hw : ∀ r, 0 < w r) (n : ℕ) :
    boundary w (locate hw n) ≤ n ∧ n < boundary w (locate hw n + 1) := by
  refine ⟨?_, Nat.find_spec (boundary_unbounded hw n)⟩
  cases he : locate hw n with
  | zero => exact Nat.zero_le _
  | succ r =>
    apply Nat.le_of_not_gt
    intro h
    have hf := Nat.find_min' (boundary_unbounded hw n) h
    change locate hw n ≤ r at hf
    omega

theorem locate_eq {w : ℕ → ℕ} (hw : ∀ r, 0 < w r) {n r : ℕ}
    (hl : boundary w r ≤ n) (hu : n < boundary w (r+1)) : locate hw n = r := by
  have h := locate_bounds hw n
  rcases lt_trichotomy (locate hw n) r with hlt | heq | hgt
  · have := (boundary_mono hw).monotone hlt
    exact False.elim (Nat.not_lt_of_ge hl (h.2.trans_le this))
  · exact heq
  · have := (boundary_mono hw).monotone hgt
    exact False.elim (Nat.not_lt_of_ge (this.trans h.1) hu)

structure Rounds where
  width : ℕ → ℕ
  width_pos : ∀ r, 0 < width r
  auxiliary : ℕ → ℕ
  /-- Select a channel and index in this round; its code is twice the local
  index plus the channel bit. -/
  reserved : (r : ℕ) → Fin (2 * width r)

namespace Rounds

variable (s : Rounds)

def length (r : ℕ) := s.auxiliary r + 4 * s.width r

theorem length_pos (r : ℕ) : 0 < s.length r := by
  have := s.width_pos r
  simp only [length]
  omega

def code (k : Bool) (i : ℕ) := 2*i + (if k then 1 else 0)

private theorem code_injective {k l : Bool} {i j : ℕ} (h : code k i = code l j) :
    k = l ∧ i = j := by
  cases k <;> cases l <;> simp_all [code] <;> omega

private theorem code_lt (k : Bool) {i w : ℕ} (hi : i < w) : code k i < 2*w := by
  cases k <;> simp [code] <;> omega

/-- Exchange the reserved position with the final balanced-column position. -/
noncomputable def perm (r : ℕ) : ℕ ≃ ℕ := Equiv.swap (s.reserved r).val (2*s.width r - 1)

private theorem perm_lt (r : ℕ) {i : ℕ} (hi : i < 2*s.width r) : s.perm r i < 2*s.width r := by
  have hw := s.width_pos r
  have hr := (s.reserved r).isLt
  by_cases h : i = (s.reserved r).val
  · subst i
    rw [perm, Equiv.swap_apply_left]
    omega
  by_cases h' : i = 2*s.width r - 1
  · subst i
    rw [perm, Equiv.swap_apply_right]
    exact hr
  rw [perm, Equiv.swap_apply_of_ne_of_ne h h']
  exact hi

noncomputable def regularStage (g : Generator) : ℕ :=
  match g with
  | .adjacent k n =>
    let r := locate s.width_pos n
    boundary s.length r + s.auxiliary r + code k (n - boundary s.width r)
  | .balanced k n =>
    let r := locate s.width_pos n
    boundary s.length r + s.auxiliary r + 2*s.width r + s.perm r (code k (n - boundary s.width r))

def auxiliaryStage (r : ℕ) (i : Fin (s.auxiliary r)) := boundary s.length r + i.val

private theorem interval_code_lt (k : Bool) (n : ℕ) :
    code k (n - boundary s.width (locate s.width_pos n)) < 2*s.width (locate s.width_pos n) := by
  have h := locate_bounds s.width_pos n
  change _ ∧ n < boundary s.width (locate s.width_pos n) + s.width (locate s.width_pos n) at h
  exact code_lt k (by omega)

theorem regular_round (k : Bool) (n : ℕ) :
    locate s.length_pos (s.regularStage (.adjacent k n)) = locate s.width_pos n ∧
    locate s.length_pos (s.regularStage (.balanced k n)) = locate s.width_pos n := by
  let r := locate s.width_pos n
  have hi := s.interval_code_lt k n
  have hp := s.perm_lt r hi
  constructor <;> apply locate_eq s.length_pos <;>
    simp only [regularStage, boundary, length] <;> dsimp only [r] at hp <;> omega

theorem auxiliary_round (r : ℕ) (i : Fin (s.auxiliary r)) :
    locate s.length_pos (s.auxiliaryStage r i) = r := by
  apply locate_eq s.length_pos
  · exact Nat.le_add_right _ _
  · have := i.isLt
    simp only [auxiliaryStage, boundary, length]
    omega

theorem regular_injective : Function.Injective s.regularStage := by
  rintro (k | k) <;> rename_i n <;> rintro (l | l) <;> rename_i m <;> intro h
  all_goals
    have hround := congrArg (locate s.length_pos) h
    simp only [(s.regular_round _ _).1, (s.regular_round _ _).2] at hround
    have hn := (locate_bounds s.width_pos n).1
    have hm := (locate_bounds s.width_pos m).1
    have hcn := s.interval_code_lt k n
    have hcm := s.interval_code_lt l m
    simp only [regularStage, hround] at h
    rw [hround] at hn hcn
  · have hc := s.perm _ |>.injective (Nat.add_left_cancel h)
    obtain ⟨rfl, he⟩ := code_injective hc
    congr 1
    omega
  · omega
  · omega
  · obtain ⟨rfl, he⟩ := code_injective (Nat.add_left_cancel h)
    congr 1
    omega

private theorem consecutive {n : ℕ} (k : Bool) :
    s.regularStage (.adjacent k n) < s.regularStage (.adjacent k (n+1)) ∧
      s.regularStage (.adjacent k n) < s.regularStage (.balanced k (n+1)) := by
  let r := locate s.width_pos n
  let t := locate s.width_pos (n+1)
  have hn := locate_bounds s.width_pos n
  have hm := locate_bounds s.width_pos (n+1)
  change boundary s.width r ≤ n ∧ n < boundary s.width (r+1) at hn
  change boundary s.width t ≤ n+1 ∧ n+1 < boundary s.width (t+1) at hm
  have hrt : r ≤ t := by
    by_contra! h
    have hh : boundary s.width (t+1) ≤ boundary s.width r :=
      (boundary_mono s.width_pos).monotone h
    exact Nat.not_lt_of_ge (hh.trans (hn.1.trans (Nat.le_succ n))) hm.2
  rcases hrt.eq_or_lt with he | hlt
  · unfold regularStage
    change boundary s.length r + s.auxiliary r + code k (n - boundary s.width r) <
      boundary s.length t + s.auxiliary t + code k (n+1-boundary s.width t) ∧ _
    have hc := s.interval_code_lt k n
    change code k (n - boundary s.width r) < 2*s.width r at hc
    change _ < _ ∧ boundary s.length r + s.auxiliary r + code k (n-boundary s.width r) <
      boundary s.length t + s.auxiliary t + 2*s.width t +
        s.perm t (code k (n+1-boundary s.width t))
    rw [← he]
    constructor
    · cases k <;> simp only [code, Bool.false_eq_true, ite_false, ite_true] <;> omega
    · omega
  · have hu := (locate_bounds s.length_pos (s.regularStage (.adjacent k n))).2
    have hv := (locate_bounds s.length_pos (s.regularStage (.adjacent k (n+1)))).1
    have hw := (locate_bounds s.length_pos (s.regularStage (.balanced k (n+1)))).1
    rw [(s.regular_round _ _).1] at hu hv
    rw [(s.regular_round _ _).2] at hw
    exact ⟨hu.trans_le (((boundary_mono s.length_pos).monotone hlt).trans hv),
      hu.trans_le (((boundary_mono s.length_pos).monotone hlt).trans hw)⟩

private theorem exists_code {w z : ℕ} (hz : z < 2*w) :
    ∃ (k : Bool) (i : ℕ), i < w ∧ code k i = z := by
  by_cases h : z % 2 = 0
  · refine ⟨false, z/2, by omega, ?_⟩
    simp only [code, Bool.false_eq_true, ite_false]
    omega
  · refine ⟨true, z/2, by omega, ?_⟩
    simp only [code, ite_true]
    omega

/-- Stages assigned to different auxiliary slots are distinct, even when
the number of auxiliaries changes between rounds. -/
theorem auxiliary_injective {r t : ℕ} {i : Fin (s.auxiliary r)} {j : Fin (s.auxiliary t)}
    (h : s.auxiliaryStage r i = s.auxiliaryStage t j) : r = t ∧ i.val = j.val := by
  have hr := congrArg (locate s.length_pos) h
  rw [s.auxiliary_round, s.auxiliary_round] at hr
  subst t
  exact ⟨rfl, Nat.add_left_cancel h⟩

/-- The auxiliary slots are disjoint from both families of regular generators. -/
theorem auxiliary_ne_regular (r : ℕ) (i : Fin (s.auxiliary r)) (g : Generator) :
    s.auxiliaryStage r i ≠ s.regularStage g := by
  intro h
  have hr := congrArg (locate s.length_pos) h
  rw [s.auxiliary_round] at hr
  have hi := i.isLt
  cases g with
  | adjacent k n =>
    rw [(s.regular_round k n).1] at hr
    simp only [auxiliaryStage, regularStage, ← hr] at h
    omega
  | balanced k n =>
    rw [(s.regular_round k n).2] at hr
    simp only [auxiliaryStage, regularStage, ← hr] at h
    omega

/-- Every polynomial stage in the concatenation has a column. In particular
there are no unnamed gaps between the designated last columns. -/
theorem stages_exhaustive (stage : ℕ) :
    (∃ r i, s.auxiliaryStage r i = stage) ∨ ∃ g, s.regularStage g = stage := by
  let r := locate s.length_pos stage
  let base := boundary s.length r
  let a := s.auxiliary r
  let w := s.width r
  have hb := locate_bounds s.length_pos stage
  change base ≤ stage ∧ stage < base + (a + 4*w) at hb
  have loc (j : ℕ) (hj : j < w) : locate s.width_pos (boundary s.width r + j) = r := by
    apply locate_eq s.width_pos (Nat.le_add_right _ _)
    exact Nat.add_lt_add_left hj _
  by_cases first : stage < base + a
  · exact Or.inl ⟨r, ⟨stage-base, by omega⟩, by change base + (stage-base) = stage; omega⟩
  right
  by_cases middle : stage < base + a + 2*w
  · obtain ⟨k, j, hj, he⟩ := exists_code (w := w) (z := stage - (base+a)) (by omega)
    refine ⟨.adjacent k (boundary s.width r + j), ?_⟩
    simp only [regularStage, loc j hj, Nat.add_sub_cancel_left, he]
    change base + a + (stage - (base+a)) = stage
    omega
  · let z := stage - (base + a + 2*w)
    have hz : z < 2*w := by dsimp [z]; omega
    have hp := s.perm_lt r hz
    obtain ⟨k, j, hj, he⟩ := exists_code hp
    refine ⟨.balanced k (boundary s.width r + j), ?_⟩
    simp only [regularStage, loc j hj, Nat.add_sub_cancel_left, he]
    have hinv : s.perm r (s.perm r z) = z := by simp [perm]
    rw [hinv]
    change base + a + 2*w + (stage - (base+a+2*w)) = stage
    omega

/-- The final raw in a block is precisely the reserved balanced column. Its
relative unit values may therefore be specified after the other factors. -/
theorem reserved_last (r : ℕ) (k : Bool) {i : ℕ} (hi : i < s.width r)
    (he : code k i = (s.reserved r).val) :
    s.regularStage (.balanced k (boundary s.width r+i)) + 1 = boundary s.length (r+1) := by
  have hl : locate s.width_pos (boundary s.width r+i) = r :=
    locate_eq s.width_pos (Nat.le_add_right _ _) (Nat.add_lt_add_left hi _)
  simp only [regularStage, hl, Nat.add_sub_cancel_left, he]
  have hperm : s.perm r (s.reserved r).val = 2*s.width r-1 := Equiv.swap_apply_left _ _
  rw [hperm]
  simp only [boundary, length]
  have := s.width_pos r
  omega

theorem exists_reserved_last (r : ℕ) :
    ∃ k i, i < s.width r ∧ code k i = (s.reserved r).val ∧
      s.regularStage (.balanced k (boundary s.width r+i)) + 1 = boundary s.length (r+1) := by
  obtain ⟨k, i, hi, he⟩ := exists_code (s.reserved r).isLt
  exact ⟨k, i, hi, he, s.reserved_last r k hi he⟩

/-- An interval may have arbitrary size, and so contains every desired regular
site up through any requested finite upper index by taking a sufficiently
large next boundary. -/
theorem regular_before_boundary (r : ℕ) (k : Bool) (i : ℕ) (hi : i < boundary s.width r) :
    s.regularStage (.adjacent k i) < boundary s.length r ∧
      s.regularStage (.balanced k i) < boundary s.length r := by
  have h := locate_bounds s.width_pos i
  have hr : locate s.width_pos i < r := by
    by_contra! hn
    have hb := (boundary_mono s.width_pos).monotone hn
    omega
  have hbound := (boundary_mono s.length_pos).monotone hr
  have hq := (locate_bounds s.length_pos (s.regularStage (.adjacent k i))).2
  have hb := (locate_bounds s.length_pos (s.regularStage (.balanced k i))).2
  rw [(s.regular_round k i).1] at hq
  rw [(s.regular_round k i).2] at hb
  exact ⟨hq.trans_le hbound, hb.trans_le hbound⟩

/-- The infinite concatenation satisfies the precedence rules used to extract
a bounded word with a positive latest exponent. -/
noncomputable def schedule : DyadicEscape.Schedule where
  stage := s.regularStage
  injective := s.regular_injective
  adjacent_succ k _ := (s.consecutive k).1
  balanced_succ k _ := (s.consecutive k).2

end Rounds

end UnconditionalCounterexample.DyadicBlocks
