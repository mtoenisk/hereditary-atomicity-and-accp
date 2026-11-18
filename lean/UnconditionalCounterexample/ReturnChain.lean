import UnconditionalCounterexample.ReturnPrefix

/-!
# The actual return sequence of a coherent raw construction

These are the canonical b/q/a objects on the one persistent raw/exponent chain.
Prefix agreement and append identities transport the literal finite-stage
conditions to these actual global rational functions. Domain membership,
primary profile calculations and eventual divisibility are proved separately.
-/

noncomputable section
namespace UnconditionalCounterexample.RecursivePrefix.Chain
open Polynomial NormalizedWords
variable (C : Chain)

/-- The single global normalized sequence from the same persistent raw/exponent chain. -/
def generators : ℕ → RatFunc ℚ := ScheduledRecovery.generators C.raw C.exponent

def b (n : ℕ) : RatFunc ℚ := ReturnPrefix.b C.generators n

def q (n : ℕ) : RatFunc ℚ := ReturnPrefix.q C.generators n

def a (n : ℕ) : RatFunc ℚ := ReturnPrefix.a C.generators n

@[simp] theorem a_zero : C.a 0 = RatFunc.X := rfl
@[simp] theorem a_succ (n : ℕ) : C.a (n + 1) = C.a n * C.b (n + 1) / C.q n := rfl

theorem generators_ne_zero (j : ℕ) : C.generators j ≠ 0 :=
  ReturnPrefix.generators_ne_zero _ _ (fun k => (C.raw_monic k).ne_zero) j

theorem a_ne_zero (n : ℕ) : C.a n ≠ 0 := ReturnPrefix.a_ne_zero _ C.generators_ne_zero n

theorem b_ne_zero (n : ℕ) : C.b n ≠ 0 := ReturnPrefix.b_ne_zero _ C.generators_ne_zero n

theorem q_ne_zero (n : ℕ) : C.q n ≠ 0 := ReturnPrefix.q_ne_zero _ C.generators_ne_zero n

/-- Every computed earlier normalized factor agrees with the actual global factor. -/
theorem generators_agree (m j : ℕ) (hj : j < m) :
    (C.approx m).generators j = C.generators j := by
  apply ReturnPrefix.generators_congr
  · intro k hk
    exact C.rawAt_agrees m k (lt_of_le_of_lt hk hj)
  · exact C.exponentAt_agrees m j hj

theorem a_agrees (m n : ℕ) (hn : 2 * n + 1 ≤ m) : (C.approx m).a n = C.a n := by
  apply ReturnPrefix.a_congr
  intro j hj
  exact C.generators_agree m j (lt_of_lt_of_le hj hn)

theorem b_agrees (m n : ℕ) (hn : (Generator.b n).stage < m) :
    (C.approx m).b n = C.b n := C.generators_agree m _ hn

theorem q_agrees (m n : ℕ) (hn : 2 * n + 2 < m) :
    (C.approx m).q n = C.q n := C.generators_agree m _ hn

/-- The q-stage target's earlier return element is already the actual global one. -/
theorem a_agrees_before_q (n : ℕ) : (C.approx (2 * n + 2)).a n = C.a n :=
  C.a_agrees _ _ (by omega)

theorem b_succ_agrees_before_q (n : ℕ) : (C.approx (2 * n + 2)).b (n + 1) = C.b (n + 1) :=
  C.b_agrees _ _ (by simp only [Generator.stage]; omega)

/-- The newly selected normalized q is exactly the global q_n. -/
theorem q_eq_appended (n : ℕ) : C.q n = (C.next (2 * n + 2)).append.q n := by
  have h := C.q_agrees (2 * n + 2 + 1) n (by omega)
  rw [C.step] at h
  exact h.symm

/-- The local appended return is exactly the global a_(n+1). -/
theorem a_succ_eq_appended (n : ℕ) : C.a (n + 1) = (C.next (2 * n + 2)).append.a (n + 1) := by
  have h := C.a_agrees (2 * n + 2 + 1) (n + 1) (by omega)
  rw [C.step] at h
  exact h.symm

/-- A new-generator local column transports directly to the global sequence. -/
theorem generators_eq_appended (m : ℕ) :
    C.generators m = (C.next m).append.generators m := by
  have h := C.generators_agree (m + 1) m (by omega)
  rw [C.step] at h
  exact h.symm

end UnconditionalCounterexample.RecursivePrefix.Chain
