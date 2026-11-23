import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Lattice
import Mathlib.Tactic.Choose

/-!
# The lexicographic rank of a positive coordinate profile

On a product of finite rows, a sum of finitely many one-coordinate
functions attains all its row minima simultaneously. With those minima
removed, the remaining row values are natural numbers. When a summand is
removed without lowering the global minimum, these normalized row values
add coordinate by coordinate.
-/

namespace UnconditionalCounterexample.Hierarchy.Prescribed

/-- A simultaneous choice of one of the entries in every row. -/
abbrev RowPoint (m : ℕ → ℕ) := (i : ℕ) → Fin (m i + 2)

/-- A nonnegative profile in normalized form. Every row attains zero. -/
structure Profile (m : ℕ → ℕ) where
  minimum : ℕ
  support : Finset ℕ
  row (i : ℕ) : Fin (m i + 2) → ℕ
  zero_outside : ∀ i ∉ support, ∀ j, row i j = 0
  row_zero : ∀ i, ∃ j, row i j = 0

namespace Profile

variable {m : ℕ → ℕ} (p : Profile m)

def eval (x : RowPoint m) : ℕ :=
  p.minimum + ∑ i ∈ p.support, p.row i (x i)

theorem minimum_le_eval (x : RowPoint m) : p.minimum ≤ p.eval x := by
  unfold eval
  omega

theorem exists_eval_eq_minimum : ∃ x : RowPoint m, p.eval x = p.minimum := by
  choose x hx using p.row_zero
  exact ⟨x, by simp [eval, hx]⟩

/-- The total of all normalized row entries. -/
def mass : ℕ := ∑ i ∈ p.support, ∑ j, p.row i j

theorem eval_le_minimum_add_mass (x : RowPoint m) : p.eval x ≤ p.minimum + p.mass := by
  apply Nat.add_le_add_left
  exact Finset.sum_le_sum fun i _ => Finset.single_le_sum (fun _ _ => Nat.zero_le _)
    (Finset.mem_univ (x i))

theorem row_eq_zero_of_minimizer {x : RowPoint m} (hx : p.eval x = p.minimum) (i : ℕ) :
    p.row i (x i) = 0 := by
  by_cases hi : i ∈ p.support
  · have hle : p.row i (x i) ≤ ∑ a ∈ p.support, p.row a (x a) :=
      Finset.single_le_sum (f := fun a => p.row a (x a)) (fun _ _ => Nat.zero_le _) hi
    unfold eval at hx
    omega
  · exact p.zero_outside i hi _

/-- Moving just one coordinate away from a minimizer reads that row entry. -/
theorem eval_update_of_minimizer {x : RowPoint m} (hx : p.eval x = p.minimum)
    (i : ℕ) (j : Fin (m i + 2)) : p.eval (Function.update x i j) = p.minimum + p.row i j := by
  unfold eval
  congr 1
  by_cases hi : i ∈ p.support
  · rw [Finset.sum_eq_single i]
    · simp
    · intro k _ hk
      rw [Function.update_of_ne hk]
      exact p.row_eq_zero_of_minimizer hx k
    · simp [hi]
  · rw [p.zero_outside i hi]
    refine Finset.sum_eq_zero fun k hk => ?_
    rw [Function.update_of_ne (show k ≠ i from fun h => hi (h ▸ hk))]
    exact p.row_eq_zero_of_minimizer hx k

private theorem mass_over (s : Finset ℕ) (h : p.support ⊆ s) :
    p.mass = ∑ i ∈ s, ∑ j, p.row i j := by
  exact Finset.sum_subset h fun i _ hi => by simp [p.zero_outside i hi]

private theorem mass_add {g k : Profile m}
    (rows : ∀ i j, p.row i j = g.row i j + k.row i j) : p.mass = g.mass + k.mass := by
  let s := p.support ∪ g.support ∪ k.support
  rw [p.mass_over s (by intro i hi; simp [s, hi]),
    g.mass_over s (by intro i hi; simp [s, hi]),
    k.mass_over s (by intro i hi; simp [s, hi])]
  simp_rw [rows, Finset.sum_add_distrib]

/-- The second component includes the sum of the nonnegative guard orders. -/
def rank (guardMass : ℕ) : ℕ × ℕ := (p.minimum, p.mass + guardMass)

/-- Removing a summand of positive profile or positive guard mass lowers
the rank in the lexicographic order. -/
theorem rank_lt_of_add (g k : Profile m) (b d : ℕ)
    (hsum : ∀ x, p.eval x = g.eval x + k.eval x)
    (hnonzero : (∃ x, 0 < k.eval x) ∨ 0 < d) :
    Prod.Lex (· < ·) (· < ·) (g.rank b) (p.rank (b + d)) := by
  obtain ⟨x, hx⟩ := p.exists_eval_eq_minimum
  have h := hsum x
  have hg := g.minimum_le_eval x
  by_cases hlt : g.minimum < p.minimum
  · exact Prod.Lex.left _ _ hlt
  have hmin : p.minimum = g.minimum := by omega
  have hxg : g.eval x = g.minimum := by omega
  have hxk : k.eval x = k.minimum := by have := k.minimum_le_eval x; omega
  have hk : k.minimum = 0 := by omega
  have rows (i : ℕ) (j : Fin (m i + 2)) : p.row i j = g.row i j + k.row i j := by
    have he := hsum (Function.update x i j)
    rw [p.eval_update_of_minimizer hx, g.eval_update_of_minimizer hxg,
      k.eval_update_of_minimizer hxk] at he
    omega
  have masses := p.mass_add rows
  have hpos : 0 < k.mass + d := by
    obtain ⟨y, hy⟩ | hd := hnonzero
    · have := k.eval_le_minimum_add_mass y
      omega
    · omega
  dsimp [rank]
  rw [hmin]
  exact Prod.Lex.right _ (by omega)

/-- Normalize a positive profile presented with a freely chosen integer
constant and finitely many arbitrary integer row functions. -/
theorem exists_of_integer_rows (s : Finset ℕ) (c : ℤ)
    (v : (i : ℕ) → Fin (m i + 2) → ℤ)
    (hnonneg : ∀ x : RowPoint m, 0 ≤ c + ∑ i ∈ s, v i (x i)) :
    ∃ p : Profile m, ∀ x, (p.eval x : ℤ) = c + ∑ i ∈ s, v i (x i) := by
  classical
  choose z hz using fun i => Finite.exists_min (v i)
  let p : Profile m := {
    minimum := (c + ∑ i ∈ s, v i (z i)).toNat
    support := s
    row := fun i j => if i ∈ s then (v i j - v i (z i)).toNat else 0
    zero_outside := fun i hi _ => by simp [hi]
    row_zero := fun i => ⟨z i, by simp⟩ }
  refine ⟨p, fun x => ?_⟩
  change (((c + ∑ i ∈ s, v i (z i)).toNat +
    ∑ i ∈ s, (if i ∈ s then (v i (x i) - v i (z i)).toNat else 0) : ℕ) : ℤ) = _
  rw [Nat.cast_add, Nat.cast_sum, Int.toNat_of_nonneg (hnonneg z)]
  have hr : (∑ i ∈ s, ((if i ∈ s then (v i (x i) - v i (z i)).toNat else 0 : ℕ) : ℤ)) =
      ∑ i ∈ s, (v i (x i) - v i (z i)) := by
    apply Finset.sum_congr rfl
    exact fun i hi => by simp [hi, Int.toNat_of_nonneg (sub_nonneg.mpr (hz i _))]
  rw [hr, Finset.sum_sub_distrib]
  omega

end Profile
end UnconditionalCounterexample.Hierarchy.Prescribed
