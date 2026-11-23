import UnconditionalCounterexample.Variations.DyadicLedger

/-!
# Completion of finite blocks on the changing raw prefix

Between two round openings the raw queue can only lose its head. Each finite
block therefore finishes at the indicated actual stage, even if its length and
width depend on all earlier polynomial choices.
-/

namespace UnconditionalCounterexample.Variations.DyadicLedger.Driver

variable (D : Driver)

/-- If an earlier round selected this column for its next slot, it is the
column emitted by this stage's actual polynomial selection. -/
theorem column_of_pending {n : ℕ} {c : RawColumn} {cs : List RawColumn}
    (hc : (D.state n).remaining = c :: cs) :
    (D.actualRequest n).column = c ∧ (D.state (n+1)).remaining = cs ∧
      (D.state (n+1)).rounds = (D.state n).rounds ∧
      (D.state (n+1)).regularBound = (D.state n).regularBound := by
  have hn : (D.state n).remaining ≠ [] := fun h => List.cons_ne_nil _ _ (hc.symm.trans h)
  obtain ⟨hopen, hw⟩ := (D.actualRequest n).keep_block hn
  have hfront := (D.actualRequest n).front
  rw [hc, hopen] at hfront
  rw [D.state_succ]
  have hcol : (D.actualRequest n).column = c := by simpa using hfront.symm
  simp [Request.update, hc, hopen, hw, hcol]

/-- Draining a finite queue fixes the next opening and preserves the accumulated
counts while all its remaining columns are emitted. -/
theorem drain (n : ℕ) :
    let t := n + (D.state n).remaining.length
    (D.state t).remaining = [] ∧ (D.state t).rounds = (D.state n).rounds ∧
      (D.state t).regularBound = (D.state n).regularBound := by
  generalize h : (D.state n).remaining.length = k
  induction k generalizing n with
  | zero => simp_all
  | succ k ih =>
    cases hc : (D.state n).remaining with
    | nil => simp [hc] at h
    | cons c cs =>
      obtain ⟨_, hnext, hr, hb⟩ := D.column_of_pending hc
      have he : (D.state (n+1)).remaining.length = k := by simpa [hnext, hc] using h
      have hm := ih (n+1) he
      simpa [show n + (k+1) = n+1+k by omega, hr, hb] using hm

/-- Raw-stage index immediately before the indicated finite batch of work. -/
noncomputable def opening : ℕ → ℕ
  | 0 => 0
  | r+1 => opening r + 1 + (D.state (opening r + 1)).remaining.length

theorem opening_empty (r : ℕ) : (D.state (D.opening r)).remaining = [] := by
  cases r with
  | zero => rfl
  | succ r => exact (D.drain (D.opening r + 1)).1

theorem opening_strict : StrictMono D.opening := by
  apply strictMono_nat_of_lt_succ
  intro r
  rw [opening]
  omega

theorem opening_rounds (r : ℕ) : (D.state (D.opening r)).rounds = r := by
  induction r with
  | zero => rfl
  | succ r ih =>
    rw [opening, (D.drain (D.opening r + 1)).2.1, D.state_succ]
    simp [Request.update, D.opening_empty r, ih]

theorem opening_bound_succ (r : ℕ) :
    (D.state (D.opening (r+1))).regularBound = (D.state (D.opening r)).regularBound +
      (D.actualRequest (D.opening r)).width := by
  rw [opening, (D.drain (D.opening r + 1)).2.2, D.state_succ]
  rfl

/-- Every regular index is below the running bound at some completed round. -/
theorem cofinal_regular_bound (i : ℕ) : ∃ r, i < (D.state (D.opening r)).regularBound := by
  have h : StrictMono (fun r => (D.state (D.opening r)).regularBound) :=
    strictMono_nat_of_lt_succ (fun r => by
      rw [D.opening_bound_succ]
      exact Nat.lt_add_of_pos_right ((D.actualRequest (D.opening r)).positive_width (D.opening_empty r)))
  exact ⟨i+1, (Nat.lt_succ_self i).trans_le (h.id_le _)⟩

end UnconditionalCounterexample.Variations.DyadicLedger.Driver
