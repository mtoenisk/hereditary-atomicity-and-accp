import UnconditionalCounterexample.Variations.DyadicHistory
import UnconditionalCounterexample.Variations.DyadicLabels
import UnconditionalCounterexample.Variations.UnivariateValues

/-!
# Frozen factors, permanent weights, and queued splits on one selection

At a raw stage, fresh primary roles and the frozen list are assigned before
choosing coefficients. The normalized polynomial is prescribed a single dyadic
column at every processed primary, and unit order at each guard. Unit factors
and precision in the local targets are free. A pending split can reserve the
balanced raw which was actually chosen.
-/

noncomputable section
namespace UnconditionalCounterexample.Variations.DyadicLedger

open GuardSupport PrimaryChoices RecursivePrefix CombinedGuardStep Univariate Polynomial

/-- The auxiliary label includes its actual prime and the regular coordinate
where its signed correction is made. -/
inductive RawColumn where
  | balanced (channel : Bool) (index : ℕ)
  | adjacent (channel : Bool) (index : ℕ)
  | auxiliary (prime : PrimeIndex) (channel : Bool) (index : ℕ) (positive : Bool)
  deriving DecidableEq

/-- Additive order prescribed at the primary. Guards always have order zero. -/
def RawColumn.atPrimary (col : RawColumn) (p : PrimeIndex) (role : Option FibreRole) : ℤ :=
  match col, role with
  | .balanced k n, some (.regular _ l j) => if k = l ∧ n = j then 1 else 0
  | .adjacent k n, some (.regular false l j) =>
      if k ≠ l then 0 else if j = n then -1 else if j = n+1 then 2 else 0
  | .auxiliary _ k n ε, some (.regular false l j) =>
      if k = l ∧ j = n then (if ε then -1 else 1) else 0
  | .auxiliary q _ _ _, some (.auxiliary _ _ _) => if p = q then 1 else 0
  | _, _ => 0

structure SplitTask where
  element : RatFunc ℚ
  modulus : ℕ
  positive : 0 < modulus

/-- Data fixed before a split block emits its first polynomial. The coefficient
of the reserved balanced raw is one. The finite-support word is evaluated on
the actual chosen normalized polynomials as the block drains. -/
structure SplitInstruction where
  task : SplitTask
  coarse : (RatFunc ℚ)ˣ
  coefficients : RawColumn →₀ ℤ
  first : ℕ → Bool
  channel : Bool
  index : ℕ
  exponent_one : coefficients (.balanced channel index) = 1

structure Ledger where
  role : PrimeIndex → Option FibreRole
  frozen : Finset ℚ[X]
  raws : List (RawColumn × ℚ[X])
  pending : List SplitTask
  reserved : List (ℕ × SplitTask)
  remaining : List RawColumn := []
  rounds : ℕ := 0
  regularBound : ℕ := 0
  activeSplit : Option SplitInstruction := none

def Ledger.initial : Ledger := ⟨fun _ => none, ∅, [], [], [], [], 0, 0, none⟩

/-- Finite work for one raw. New regular labels are globally fresh. The local
polynomial targets on an auxiliary raw use the metadata of its actual site. -/
structure FreshFibres {n : ℕ} (m : Ledger) (P : Prefix n) where
  births : Births P
  role : ∀ p, p ∈ births.primes → Option FibreRole
  paired : ∀ p hp, (births.site p hp).paired ↔ (role p hp).isSome
  primary_before : ∀ p hp, (births.site p hp).paired → ∀ j : Fin n,
    ‖(P.raw j).eval₂ (algebraMap ℚ ℚ_[p.val]) ((births.site p hp).branch false)‖ = 1
  new_regular : ∀ p hp c k i, role p hp = some (.regular c k i) →
    ∀ q, m.role q ≠ some (.regular c k i)
  distinct_regular : ∀ p hp q hq c k i, role p hp = some (.regular c k i) →
    role q hq = some (.regular c k i) → p = q

/-- The frozen factors, raw column and pending tasks at a single polynomial stage. -/
structure Request {n : ℕ} (m : Ledger) (P : Prefix n) extends FreshFibres m P where
  freeze : Finset ℚ[X]
  freeze_new : ∀ f ∈ freeze, ∀ j : Fin n, P.raw j ≠ f
  column : RawColumn
  /-- Fill a whole finite block at a round opening, then consume it in order. -/
  openBlock : List RawColumn
  width : ℕ
  keep_block : m.remaining ≠ [] → openBlock = [] ∧ width = 0
  positive_width : m.remaining = [] → 0 < width
  front : (m.remaining ++ openBlock).head? = some column
  install : Option SplitInstruction := none
  install_open : m.remaining ≠ [] → install = none
  enqueue : List SplitTask := []
  reserve : Bool := false
  reserve_last : reserve = true → (m.remaining ++ openBlock).tail = []
  reserve_balanced : reserve = true → ∃ k i, column = .balanced k i
  reserve_primes : reserve = true → ∀ t, (m.pending ++ enqueue).head? = some t →
    ∀ p : PrimeIndex, p.val ∣ t.modulus → p ∈ P.state.assignment.primes ∪ births.primes

namespace Request

variable {n : ℕ} {m : Ledger} {P : Prefix n} (r : Request m P)

/-- At old primes keep the stored role. Unrequested new guards have no role. -/
def nextRole (p : PrimeIndex) : Option FibreRole :=
  if h : p ∈ r.births.primes then r.role p h else m.role p

def update (raw : ℚ[X]) : Ledger where
  role := r.nextRole
  remaining := (m.remaining ++ r.openBlock).tail
  rounds := if m.remaining.isEmpty then m.rounds + 1 else m.rounds
  regularBound := m.regularBound + r.width
  activeSplit := if (m.remaining ++ r.openBlock).tail.isEmpty then none
    else r.install.or m.activeSplit
  frozen := m.frozen ∪ r.freeze
  raws := (r.column, raw) :: m.raws
  pending := if r.reserve then (m.pending ++ r.enqueue).tail else m.pending ++ r.enqueue
  reserved := if r.reserve then ((m.pending ++ r.enqueue).head?.map (n, ·)).toList ++ m.reserved
    else m.reserved

end Request

/-- Raw prescriptions may choose any p-adic integral unit multiplier and any
precision at any processed branch, after the new evaluations are known. -/
structure Driver where
  request : ∀ {n} (m : Ledger) (P : Prefix n), Table P.state.assignment.primes → Request m P
  base : ∀ {n} (_m : Ledger) (P : Prefix n) (_start : n = 0 → P.state = zeroState) (d : ℕ)
    (needed : Finset PrimeIndex), {B : Batch // StageRecursion.BatchProgress P d needed B}
  unit : ∀ {n} (_m : Ledger) (P : Prefix n), Table P.state.assignment.primes →
    (B : Batch) → Table B.assigned.primes → (j : B.indices) → Bool → ℤ_[B.primeAt j]ˣ
  precision : ∀ {n} (_m : Ledger) (P : Prefix n), Table P.state.assignment.primes →
    (B : Batch) → Table B.assigned.primes → B.indices → Bool → ℕ

namespace Driver

variable (D : Driver)

private def localTargets {n : ℕ} (m : Ledger) (P : Prefix n) (old : Table P.state.assignment.primes)
    (B : Batch) (sites : Table B.assigned.primes) : Targets B sites where
  value j b :=
    let r := D.request m P old
    let p := primes j.val
    let z := if b then 0 else r.column.atPrimary p (r.nextRole p)
    ((B.primeAt j : ℚ_[B.primeAt j]) ^ z) * ((D.unit m P old B sites j b : ℤ_[B.primeAt j]) : ℚ_[B.primeAt j])
  precision := D.precision m P old B sites
  nonzero j b _ := by
    apply mul_ne_zero
    · apply zpow_ne_zero
      exact Nat.cast_ne_zero.mpr (Fact.out (p := (B.primeAt j).Prime)).ne_zero
    · exact fun h => (D.unit m P old B sites j b).ne_zero (Subtype.ext h)

def program : DyadicHistory.Program Ledger where
  initial := Ledger.initial
  prescribe m :=
    { degreeFloor := fun P old => (m.frozen ∪ (D.request m P old).freeze).sup Polynomial.natDegree
      births := fun P old => (D.request m P old).births
      base := D.base m
      targets := D.localTargets m }
  observe m P old s _ := (D.request m P old).update s.raw

abbrev schedule := D.program.schedule
abbrev requirements := D.schedule.requirements
abbrev state (n : ℕ) := D.program.memory n
abbrev actualRequest (n : ℕ) := D.request (D.state n) ((chain D.requirements).approx n)
  (table D.requirements n)

theorem actualTarget_value (n : ℕ) (j : (selection D.requirements n).batch.indices) (b : Bool) :
    (actualTargets D.requirements n).value j b =
      ((selection D.requirements n).batch.primeAt j : ℚ_[(selection D.requirements n).batch.primeAt j]) ^
        (if b then (0 : ℤ) else (D.actualRequest n).column.atPrimary (primes j.val)
          ((D.actualRequest n).nextRole (primes j.val))) *
      (D.unit (D.state n) ((chain D.requirements).approx n) (table D.requirements n)
        (selection D.requirements n).batch (table D.requirements (n+1)) j b).val.val := rfl

theorem actualTarget_precision (n : ℕ) (j : (selection D.requirements n).batch.indices) (b : Bool) :
    (actualTargets D.requirements n).precision j b = D.precision (D.state n)
      ((chain D.requirements).approx n) (table D.requirements n) (selection D.requirements n).batch
      (table D.requirements (n+1)) j b := rfl

/-- The recorded member is the actual selected polynomial under the requested
column. Freezing and reservations advance in the same successor. -/
theorem state_succ (n : ℕ) :
    D.state (n+1) = (D.actualRequest n).update ((chain D.requirements).raw n) := by
  rw [state, DyadicHistory.Program.memory_succ, raw_eq_selection]
  rfl

theorem chosen_eq (n : ℕ) : D.schedule.chosen n = (D.actualRequest n).births := rfl

theorem retained (n : ℕ) (f : ℚ[X]) (hf : f ∈ (D.actualRequest n).freeze) :
    f ∉ Set.range (chain D.requirements).raw := by
  apply retained_after_freezing D.requirements n f ((D.actualRequest n).freeze_new f hf)
  exact Finset.le_sup (f := Polynomial.natDegree) (Finset.mem_union_right (D.state n).frozen hf)

/-- A prime outside the actual finite table has no assigned dyadic role. -/
theorem role_none_of_unassigned (n : ℕ) (p : PrimeIndex)
    (hp : p ∉ ((chain D.requirements).approx n).state.assignment.primes) :
    (D.state n).role p = none := by
  induction n with
  | zero => rfl
  | succ n ih =>
    let s := selection D.requirements n
    have hnew : p ∉ (D.actualRequest n).births.primes := fun h =>
      hp (s.batch.processed_subset_assigned (D.schedule.requested_processed n h))
    have hold : p ∉ ((chain D.requirements).approx n).state.assignment.primes := fun h =>
      hp (s.toNext.assigned_subset h)
    rw [state_succ]
    simpa [Request.update, Request.nextRole, hnew] using ih hold

/-- Extending the assigned table preserves every older label. -/
theorem role_old (n : ℕ) (p : PrimeIndex)
    (hp : p ∈ ((chain D.requirements).approx n).state.assignment.primes) :
    (D.state (n+1)).role p = (D.state n).role p := by
  have hnew : p ∉ (D.actualRequest n).births.primes := fun h =>
    (D.actualRequest n).births.fresh p h hp
  rw [state_succ]
  simp [Request.update, Request.nextRole, hnew]

/-- The role fixed at birth persists through all later raw and split stages. -/
theorem role_persistent {n : ℕ} (p : PrimeIndex) (hp : p ∈ (D.actualRequest n).births.primes)
    {t : ℕ} (ht : n < t) : (D.state t).role p = (D.actualRequest n).role p hp := by
  induction t, ht using Nat.le_induction with
  | base => rw [state_succ]; simp [Request.update, Request.nextRole, hp]
  | succ t ht ih =>
    have hn : p ∉ (D.actualRequest t).births.primes := fun h =>
      (Nat.ne_of_lt ht) (D.schedule.requested_unique hp h)
    rw [state_succ]
    simpa [Request.update, Request.nextRole, hn] using ih

/-- The very same role is attached to the literal permanent evaluation site. -/
theorem permanent_role {n : ℕ} (p : PrimeIndex) (hp : p ∈ (D.actualRequest n).births.primes) :
    permanentSite D.requirements p = (D.actualRequest n).births.site p hp ∧
      ∀ t > n, (D.state t).role p = (D.actualRequest n).role p hp :=
  ⟨D.schedule.permanentSite_requested n p hp, fun _ ht => D.role_persistent p hp ht⟩

end Driver
end UnconditionalCounterexample.Variations.DyadicLedger
