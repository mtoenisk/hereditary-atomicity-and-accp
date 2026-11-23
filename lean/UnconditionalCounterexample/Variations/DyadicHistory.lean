import UnconditionalCounterexample.Variations.UnivariateBirths

/-!
# Carrying calibration and splitting history on the univariate selection

The raw prefix records the exact batches and polynomials. At every reachable
successor this determines a unique preceding prefix and the actual last raw,
exponent and batch. Replaying its recorded steps gives both the permanent
fibre table and the application state. Thus births and targets can inspect the
stored history and the resulting schedule uses the ordinary univariate chain.
-/

noncomputable section
namespace UnconditionalCounterexample.Variations.DyadicHistory

open RecursivePrefix CombinedGuardStep Univariate GuardSupport

private def recordedState {n : ℕ} (P : Prefix n) : State :=
  if h : n = 0 then zeroState else (P.batch ⟨n-1, by omega⟩).toState

/-- The current assignment is the most recent actual batch or the initial state. -/
def Standard {n : ℕ} (P : Prefix n) : Prop := P.state = recordedState P

private theorem empty_standard : Standard empty := rfl

private theorem append_standard {n : ℕ} {P : Prefix n} (s : Next P) : Standard s.append := by
  change s.batch.toState = (s.append.batch (Fin.last n)).toState
  rw [s.append_batch_last]

private theorem prefix_ext {n : ℕ} {P Q : Prefix n} (hr : P.raw = Q.raw)
    (he : P.exponent = Q.exponent) (hb : P.batch = Q.batch) (hs : P.state = Q.state) : P = Q := by
  cases P
  cases Q
  simp_all

private theorem next_ext {n : ℕ} {P : Prefix n} {a b : Next P} (hr : a.raw = b.raw)
    (he : a.exponent = b.exponent) (hb : a.batch = b.batch) : a = b := by
  cases a
  cases b
  simp_all

/-- A prefix together with the actual final selection data that produced the
given successor. No polynomial or prime is reselected in this decomposition. -/
private structure Parent {n : ℕ} (target : Prefix (n+1)) where
  prefixData : Prefix n
  standard : Standard prefixData
  selected : Next prefixData
  eq_append : selected.append = target

private instance {n : ℕ} (target : Prefix (n+1)) : Subsingleton (Parent target) where
  allEq := by
    rintro ⟨P, hP, a, ha⟩ ⟨Q, hQ, b, hb⟩
    have h := ha.trans hb.symm
    have hr : P.raw = Q.raw := funext fun j => by
      simpa using congrArg (fun z : Prefix (n+1) => z.raw j.castSucc) h
    have he : P.exponent = Q.exponent := funext fun j => by
      simpa using congrArg (fun z : Prefix (n+1) => z.exponent j.castSucc) h
    have hbatch : P.batch = Q.batch := funext fun j => by
      simpa using congrArg (fun z : Prefix (n+1) => z.batch j.castSucc) h
    have hstate : P.state = Q.state := by
      rw [hP, hQ]
      simp [recordedState, hbatch]
    have hPQ := prefix_ext hr he hbatch hstate
    subst Q
    have hab : a = b := next_ext
      (by simpa using congrArg (fun z : Prefix (n+1) => z.raw (Fin.last n)) h)
      (by simpa using congrArg (fun z : Prefix (n+1) => z.exponent (Fin.last n)) h)
      (by simpa using congrArg (fun z : Prefix (n+1) => z.batch (Fin.last n)) h)
    subst b
    rfl

/-- The state update may inspect the entire preceding table, the polynomial
and exponent just selected, and the final table of that very batch. -/
structure Program (M : Type*) where
  initial : M
  prescribe : M → Schedule
  observe : ∀ {n} (_m : M) (P : Prefix n), Table P.state.assignment.primes →
    (s : Next P) → Table s.batch.assigned.primes → M

variable {M : Type*} (D : Program M)

private def initialTable {n : ℕ} (P : Prefix n) : Table P.state.assignment.primes :=
  fun p hp => ⟨(P.state.assignment.guard p hp).value,
    (P.state.assignment.guard p hp).transcendental, none⟩

private def advance {n : ℕ} (P : Prefix n) (old : Table P.state.assignment.primes × M)
    (s : Next P) : Table s.append.state.assignment.primes × M :=
  let newTable := extend (D.prescribe old.2).requirements P old.1 s.batch
  (newTable, D.observe old.2 P old.1 s newTable)

/-- The replay is total on all structural prefixes, including prefixes outside
the constructed chain. Its successor rule below completely determines its
value on every reachable prefix. -/
private def replay : {n : ℕ} → (P : Prefix n) → Table P.state.assignment.primes × M
  | 0, P => (initialTable P, D.initial)
  | _+1, P => by
    classical
    exact if h : Nonempty (Parent P) then
      let q := Classical.choice h
      q.eq_append ▸ advance D q.prefixData (replay q.prefixData) q.selected
    else (initialTable P, D.initial)

private theorem replay_append {n : ℕ} (P : Prefix n) (hP : Standard P) (s : Next P) :
    replay D s.append = advance D P (replay D P) s := by
  let q : Parent s.append := ⟨P, hP, s, rfl⟩
  have h : Nonempty (Parent s.append) := ⟨q⟩
  rw [replay, dite_eq_left h]
  have eq : Classical.choice h = q := Subsingleton.elim ..
  rw [eq]

/-- A single U schedule executes the history-sensitive prescription. -/
def Program.schedule : Schedule where
  degreeFloor P old := (D.prescribe (replay D P).2).degreeFloor P old
  births P old := (D.prescribe (replay D P).2).births P old
  base P start d needed := (D.prescribe (replay D P).2).base P start d needed
  targets P old B sites := (D.prescribe (replay D P).2).targets P old B sites

namespace Program

private theorem actual_standard (n : ℕ) :
    Standard ((chain D.schedule.requirements).approx n) := by
  cases n with
  | zero => exact empty_standard
  | succ n => exact append_standard (selection D.schedule.requirements n).toNext

private theorem replay_table (n : ℕ) :
    (replay D ((chain D.schedule.requirements).approx n)).1 = table D.schedule.requirements n := by
  induction n with
  | zero =>
    funext p hp
    exact (Finset.notMem_empty p hp).elim
  | succ n ih =>
    let R := D.schedule.requirements
    let P := (chain R).approx n
    let sel := selection R n
    change (replay D sel.toNext.append).1 = extend R P (table R n) sel.batch
    rw [replay_append D P (D.actual_standard n) sel.toNext]
    change extend (D.prescribe (replay D P).2).requirements P (replay D P).1 sel.batch = _
    change (replay D P).1 = table R n at ih
    rw [ih]
    rfl

/-- Application memory just before selecting raw `n` in the actual U chain. -/
def memory (n : ℕ) : M := (replay D ((chain D.schedule.requirements).approx n)).2

@[simp] theorem memory_zero : D.memory 0 = D.initial := rfl

/-- The update sees the same selected raw, processing batch, and site table
used by the permanent valuations and all downstream U transfer theorems. -/
theorem memory_succ (n : ℕ) :
    D.memory (n+1) = D.observe (D.memory n) ((chain D.schedule.requirements).approx n)
      (table D.schedule.requirements n) (selection D.schedule.requirements n).toNext
      (table D.schedule.requirements (n+1)) := by
  let R := D.schedule.requirements
  let P := (chain R).approx n
  let sel := selection R n
  change (replay D sel.toNext.append).2 = _
  rw [replay_append D P (D.actual_standard n) sel.toNext]
  change D.observe (D.memory n) P (replay D P).1 sel.toNext
    (extend (D.prescribe (D.memory n)).requirements P (replay D P).1 sel.batch) = _
  rw [D.replay_table n]
  rfl

end Program
end UnconditionalCounterexample.Variations.DyadicHistory
