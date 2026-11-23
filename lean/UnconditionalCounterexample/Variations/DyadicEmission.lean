import UnconditionalCounterexample.Variations.DyadicRoundWork

/-!
# Actual raw stages emit the concatenated dyadic blocks

The changing ledger emits exactly the column at the given offset of its
opening block. Its regular stage map is the injective dyadic schedule, with
the same predecessor inequalities and reserved final raw, and the auxiliary
slots account for all remaining stages.
-/

noncomputable section
namespace UnconditionalCounterexample.Variations.DyadicLedger

open DyadicBlocks DyadicEscape

namespace Driver
variable (D : Driver)

private theorem emitted_from_queue {n i : ℕ} {c : RawColumn}
    (h : (D.state n).remaining[i]? = some c) : (D.actualRequest (n+i)).column = c := by
  induction i generalizing n with
  | zero =>
    cases hs : (D.state n).remaining with
    | nil => simp [hs] at h
    | cons d ds =>
      have hd : d = c := by simpa [hs] using h
      simpa only [Nat.add_zero,hd] using (D.column_of_pending hs).1
  | succ i ih =>
    cases hs : (D.state n).remaining with
    | nil => simp [hs] at h
    | cons d ds =>
      have hl := (D.column_of_pending hs).2.1
      have hh : (D.state (n+1)).remaining[i]? = some c := by simpa [hs,hl] using h
      change (D.actualRequest (n + (i+1))).column = c
      rw [show n + (i+1) = n+1+i by omega]
      exact ih hh

theorem emits_at_empty (n : ℕ) (empty : (D.state n).remaining = [])
    {i : ℕ} {c : RawColumn} (h : (D.actualRequest n).openBlock[i]? = some c) :
    (D.actualRequest (n + i)).column = c := by
  have front := (D.actualRequest n).front
  simp only [empty,List.nil_append] at front
  cases i with
  | zero =>
    rw [← List.head?_eq_getElem?] at h
    exact Option.some.inj (front.symm.trans h)
  | succ i =>
    have hs : (D.state (n+1)).remaining = (D.actualRequest n).openBlock.tail := by
      rw [D.state_succ]
      simp [Request.update,empty]
    have hi : (D.state (n+1)).remaining[i]? = some c := by simpa [hs,List.getElem?_tail] using h
    rw [show n+(i+1) = (n+1)+i by omega]
    exact D.emitted_from_queue hi

theorem opening_emits {r i : ℕ} {c : RawColumn} (h : (D.actualRequest (D.opening r)).openBlock[i]? = some c) :
    (D.actualRequest (D.opening r + i)).column = c :=
  D.emits_at_empty (D.opening r) (D.opening_empty r) h

theorem next_opening (r : ℕ) : D.opening (r+1) = D.opening r + (D.actualRequest (D.opening r)).openBlock.length := by
  let n := D.opening r
  have h : (D.state n).remaining = [] := D.opening_empty r
  have he := (D.actualRequest n).front
  simp only [h,List.nil_append] at he
  have hn : (D.actualRequest n).openBlock ≠ [] := by intro hz; simp [hz] at he
  have hs : (D.state (n+1)).remaining = (D.actualRequest n).openBlock.tail := by
    rw [D.state_succ]
    simp [Request.update,h]
  change n+1+(D.state (n+1)).remaining.length = _
  rw [hs,List.length_tail]
  change n+1+((D.actualRequest n).openBlock.length-1) = n+(D.actualRequest n).openBlock.length
  have := List.length_pos_iff.mpr hn
  omega

end Driver

namespace Block
variable (s : Block)

theorem get_aux (j : Fin s.auxiliary.length) : s.columns[j.val]? = some s.auxiliary[j.val] := by
  have h₁ : j.val < (s.auxiliary ++ (List.range (2*s.width)).map (s.localColumn false)).length := by simp; omega
  simp only [columns, List.getElem?_append_left h₁, List.getElem?_append_left j.isLt, List.getElem?_eq_getElem j.isLt]

theorem get_adjacent {j : ℕ} (hj : j < 2*s.width) :
    s.columns[s.auxiliary.length+j]? = some (s.localColumn false j) := by
  have hl : s.auxiliary.length+j < (s.auxiliary ++ (List.range (2*s.width)).map (s.localColumn false)).length := by simpa
  rw [columns,List.getElem?_append_left hl,List.getElem?_append_right (Nat.le_add_right _ _)]
  simp [hj]

theorem get_balanced {j : ℕ} (hj : j < 2*s.width) :
    s.columns[s.auxiliary.length+2*s.width+j]? = some (s.localColumn true (s.perm j)) := by
  have hl : (s.auxiliary ++ (List.range (2*s.width)).map (s.localColumn false)).length ≤
      s.auxiliary.length+2*s.width+j := by simp
  rw [columns,List.getElem?_append_right hl]
  simp [hj]

end Block

/-- Each block is read from the round opening, so its width and its
auxiliary primes may depend on all earlier raw choices. -/
structure Emission (D : Driver) where
  block : ℕ → Block
  opened : ∀ r, (D.actualRequest (D.opening r)).openBlock = (block r).columns
  start : ∀ r, (block r).start = (D.state (D.opening r)).regularBound
  width : ∀ r, (block r).width = (D.actualRequest (D.opening r)).width

namespace Emission
variable {D : Driver} (E : Emission D)

def rounds : Rounds where
  width r := (E.block r).width
  width_pos r := (E.block r).positive
  auxiliary r := (E.block r).auxiliary.length
  reserved r := (E.block r).reserved

theorem stage_boundary (r : ℕ) : boundary E.rounds.length r = D.opening r := by
  induction r with
  | zero => rfl
  | succ r ih => rw [boundary,ih,D.next_opening,E.opened,Block.length_columns]; rfl

theorem index_boundary (r : ℕ) : boundary E.rounds.width r = (E.block r).start := by
  induction r with
  | zero => rw [E.start]; rfl
  | succ r ih => rw [boundary,ih,E.start r,E.start (r+1),D.opening_bound_succ,← E.width]; rfl

private theorem emit {r i : ℕ} {c : RawColumn} (h : (E.block r).columns[i]? = some c) :
    (D.actualRequest (boundary E.rounds.length r+i)).column = c := by
  rw [E.stage_boundary]
  apply D.opening_emits
  rwa [E.opened]

theorem auxiliary (r : ℕ) (i : Fin (E.block r).auxiliary.length) :
    (D.actualRequest (E.rounds.auxiliaryStage r i)).column = (E.block r).auxiliary[i.val] :=
  E.emit ((E.block r).get_aux i)

def regularColumn : Generator → RawColumn
  | .adjacent k n => .adjacent k n
  | .balanced k n => .balanced k n

/-- The actual selected column at each regular schedule slot. -/
theorem regular (g : Generator) : (D.actualRequest (E.rounds.regularStage g)).column = regularColumn g := by
  obtain ⟨k,n⟩ | ⟨k,n⟩ := g
  all_goals
    let r := locate E.rounds.width_pos n
    let j := n - boundary E.rounds.width r
    have hl := locate_bounds E.rounds.width_pos n
    change boundary E.rounds.width r ≤ n ∧ n < boundary E.rounds.width r + (E.block r).width at hl
    have hj : j < (E.block r).width := by dsimp only [j]; omega
    have hcode : Rounds.code k j < 2*(E.block r).width := by cases k <;> simp [Rounds.code] <;> omega
    have hn : (E.block r).start+j = n := by rw [← E.index_boundary]; dsimp only [j]; omega
  · let s := E.block r
    let z := Rounds.code k j
    have hperm : s.perm z < 2*s.width := by
      have hr := s.reserved.isLt
      have hw := s.positive
      by_cases h : z = s.reserved.val
      · rw [Block.perm, h,Equiv.swap_apply_left]; omega
      by_cases ht : z = 2*s.width-1
      · rw [Block.perm, ht,Equiv.swap_apply_right]; exact hr
      rw [Block.perm,Equiv.swap_apply_of_ne_of_ne h ht]
      exact hcode
    have he := E.emit (s.get_balanced hperm)
    rw [show s.perm (s.perm z) = z by simp [Block.perm],s.localColumn_code,hn] at he
    change (D.actualRequest (boundary E.rounds.length r + s.auxiliary.length + 2*s.width + s.perm z)).column = .balanced k n
    rw [show boundary E.rounds.length r + s.auxiliary.length + 2*s.width + s.perm z =
      boundary E.rounds.length r + (s.auxiliary.length + 2*s.width + s.perm z) by omega]
    simpa using he
  · have he := E.emit ((E.block r).get_adjacent hcode)
    rw [Block.localColumn_code,hn] at he
    change (D.actualRequest (boundary E.rounds.length r + (E.block r).auxiliary.length + Rounds.code k j)).column = .adjacent k n
    rw [Nat.add_assoc]
    simpa using he

/-- The actual stage map is exhausted by the regular labels and the per-round
auxiliary lists; each slot has the exact indicated emitted column. -/
theorem exhaustive (n : ℕ) :
    (∃ r, ∃ i : Fin (E.block r).auxiliary.length, E.rounds.auxiliaryStage r i = n ∧
      (D.actualRequest n).column = (E.block r).auxiliary[i.val]) ∨
      ∃ g, E.rounds.regularStage g = n ∧ (D.actualRequest n).column = regularColumn g := by
  rcases E.rounds.stages_exhaustive n with ⟨r,i,rfl⟩ | ⟨g,rfl⟩
  · exact Or.inl ⟨r,i,rfl,E.auxiliary r i⟩
  · exact Or.inr ⟨g,rfl,E.regular g⟩

end Emission
end UnconditionalCounterexample.Variations.DyadicLedger
