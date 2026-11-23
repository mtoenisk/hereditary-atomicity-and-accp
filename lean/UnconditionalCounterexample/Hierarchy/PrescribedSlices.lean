import UnconditionalCounterexample.Hierarchy.PrescribedRank
import Mathlib.Tactic.FinCases

/-! # Single-coordinate slices and the two-point test for binary rows -/

namespace UnconditionalCounterexample.Hierarchy.Prescribed

variable {m : ℕ → ℕ}

/-- The indicator of the slice on which the `i`th coordinate equals `j`. -/
def sliceAt (i : ℕ) (j : Fin (m i + 2)) (x : RowPoint m) : ℕ :=
  if x i = j then 1 else 0

/-- In each row the slices sum to the constant profile one. -/
theorem sum_sliceAt (i : ℕ) (x : RowPoint m) : ∑ j, sliceAt i j x = 1 := by
  simp [sliceAt]

/-- A normalized profile dominated by a single slice is zero or that slice. -/
theorem Profile.eq_zero_or_sliceAt (p : Profile m) (i : ℕ) (j : Fin (m i + 2))
    (h : ∀ x, p.eval x ≤ sliceAt i j x) :
    (∀ x, p.eval x = 0) ∨ ∀ x, p.eval x = sliceAt i j x := by
  obtain ⟨j', hj'⟩ := exists_ne j
  have off (x : RowPoint m) : p.eval (Function.update x i j') = 0 := by
    have := h (Function.update x i j')
    simpa [sliceAt, hj'] using this
  have read (x : RowPoint m) : p.eval x = p.row i (x i) := by
    have hm := p.minimum_le_eval (Function.update x i j')
    rw [off] at hm
    have hz := Nat.eq_zero_of_le_zero hm
    have he := p.eval_update_of_minimizer ((off x).trans hz.symm) i (x i)
    simpa [hz] using he
  by_cases hj : p.row i j = 0
  · left
    intro x
    by_cases he : x i = j
    · rw [read, he, hj]
    · simpa [sliceAt, he] using h x
  · right
    intro x
    by_cases he : x i = j
    · have hle := h x
      rw [read, he] at hle
      simp [sliceAt, he] at hle ⊢
      rw [read, he]
      omega
    · simpa [sliceAt, he] using h x

/-- On binary rows the all-first and all-second points detect every
nonzero normalized profile. -/
theorem Profile.binary_eq_zero (p : Profile (fun _ => 0))
    (hfirst : p.eval (fun _ => 0) = 0) (hsecond : p.eval (fun _ => 1) = 0) :
    ∀ x, p.eval x = 0 := by
  have hle := p.minimum_le_eval (fun _ => 0)
  rw [hfirst] at hle
  have hmin := Nat.eq_zero_of_le_zero hle
  have h0 := p.row_eq_zero_of_minimizer (hfirst.trans hmin.symm)
  have h1 := p.row_eq_zero_of_minimizer (hsecond.trans hmin.symm)
  have hr (i : ℕ) (j : Fin 2) : p.row i j = 0 := by
    fin_cases j
    · exact h0 i
    · exact h1 i
  intro x
  simp [eval, hmin, hr]

end UnconditionalCounterexample.Hierarchy.Prescribed
