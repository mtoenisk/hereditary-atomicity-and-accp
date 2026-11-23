import UnconditionalCounterexample.Variations.DyadicRoundWork
import UnconditionalCounterexample.Variations.DyadicLedgerCalendar
import UnconditionalCounterexample.Variations.DyadicModulusFibres
import UnconditionalCounterexample.Variations.DyadicLedgerSplit
import UnconditionalCounterexample.Variations.DyadicSplitPrefix
import UnconditionalCounterexample.Variations.FrozenGuards

/-!
# Dispatch of finite opening data on one univariate selection

An opening freezes the current calendar and prepares the modulus of the named
split task. Interior slots consume the saved block, including the saved split
word. At its reserved final slot, the residue targets are evaluated on the
actual prefix, with the full requested prime precision.
-/

noncomputable section
namespace UnconditionalCounterexample.Variations.DyadicLedger
open GuardSupport RecursivePrefix Univariate Polynomial CombinedGuardStep FreezingCalendar

/-- No additional paired sites are needed between successive block openings. -/
def FreshFibres.empty {n : ℕ} (m : Ledger) (P : Prefix n) : FreshFibres m P where
  births :=
    { primes := ∅
      fresh := by simp
      guard := fun p h => (Finset.notMem_empty p h).elim
      birth_eq := by simp
      old_units := by simp
      primary := fun p h => (Finset.notMem_empty p h).elim }
  role := fun p h => (Finset.notMem_empty p h).elim
  paired := by simp
  primary_before := by simp
  new_regular := by simp
  distinct_regular := by simp

def taskAt (r : ℕ) : SplitTask :=
  ⟨(splitAt r).1,(splitAt r).2.val,(splitAt r).2.property⟩

/-- Opening data after selecting the finite batch of calibrated fibres and
the block's reserved coordinate. All split coefficients are retained through
the last slot. -/
structure RoundData {n : ℕ} (m : Ledger) (P : Prefix n) where
  block : Block
  start_eq : block.start = m.regularBound
  fibres : FreshFibres m P
  instruction : Option SplitInstruction
  reserved_eq : ∀ I, instruction = some I →
    block.localColumn true block.reserved.val = .balanced I.channel I.index

/-- The finite arithmetic choice at a round opening. -/
abbrev Planner := ∀ {n}, (m : Ledger) → (P : Prefix n) → Table P.state.assignment.primes → RoundData m P

def freezeList {n : ℕ} (m : Ledger) (P : Prefix n) : Finset ℚ[X] :=
  FreezingCalendar.pending P m.frozen (candidates m.rounds ∅)

private def prepare {n : ℕ} {m : Ledger} {P : Prefix n} (o : RoundData m P)
    (hempty : m.remaining = []) : Request m P where
  toFreshFibres := o.fibres.coverPrimes (FreshFibres.modulusPrimes (taskAt m.rounds).modulus)
  freeze := freezeList m P
  freeze_new := pending_fresh P m.frozen _
  column := o.block.columns.head o.block.nonempty
  openBlock := o.block.columns
  width := o.block.width
  keep_block := by simp [hempty]
  positive_width := fun _ => o.block.positive
  front := by simp [hempty,List.head?_eq_some_head o.block.nonempty]
  install := o.instruction
  install_open := by simp [hempty]
  enqueue := (o.instruction.map SplitInstruction.task).toList
  reserve_last := by simp
  reserve_balanced := by simp
  reserve_primes := by simp

/-- A split is acted on at the recorded balanced coordinate, at the end of
the block. -/
def finalInstruction (m : Ledger) (col : RawColumn) (tail : List RawColumn) : Option SplitInstruction :=
  m.activeSplit.filter fun I => decide (tail = [] ∧ col = .balanced I.channel I.index)

private def pendingPrimes (m : Ledger) : Finset PrimeIndex :=
  match m.pending.head? with
  | none => ∅
  | some t => FreshFibres.modulusPrimes t.modulus

private def consume {n : ℕ} (m : Ledger) (P : Prefix n) (c : RawColumn) (cs : List RawColumn)
    (hr : m.remaining = c::cs) : Request m P where
  toFreshFibres := (FreshFibres.empty m P).coverPrimes (pendingPrimes m)
  freeze := ∅
  freeze_new := by simp
  column := c
  openBlock := []
  width := 0
  keep_block := by simp
  positive_width := by simp [hr]
  front := by simp [hr]
  install := none
  install_open := by simp
  reserve := (finalInstruction m c cs).isSome
  reserve_last := by
    intro h
    obtain ⟨I,hI⟩ := Option.isSome_iff_exists.mp h
    obtain ⟨_,h⟩ := Option.filter_eq_some_iff.mp hI
    simpa [hr] using (of_decide_eq_true h).1
  reserve_balanced := by
    intro h
    obtain ⟨I,hI⟩ := Option.isSome_iff_exists.mp h
    obtain ⟨_,h⟩ := Option.filter_eq_some_iff.mp hI
    exact ⟨I.channel,I.index,(of_decide_eq_true h).2⟩
  reserve_primes := by
    intro _ t ht p hp
    simp only [List.append_nil] at ht
    simpa [pendingPrimes,ht] using (FreshFibres.empty m P).coverPrimes_covered
      (pendingPrimes m) (x := p) (by
        rw [pendingPrimes,ht]
        exact Finset.mem_subtype.mpr (Nat.mem_primeFactors.mpr ⟨p.property,hp,t.positive.ne'⟩))

def dispatch (choose : Planner) {n : ℕ} (m : Ledger) (P : Prefix n)
    (T : Table P.state.assignment.primes) : Request m P :=
  match h : m.remaining with
  | [] => prepare (choose m P T) h
  | c::cs => consume m P c cs h

/-- The normalized multiplier preceding the reserved raw, evaluated on the
actual polynomial prefix. The chronological label at step j is the one
saved by the same driver when that raw was selected. -/
def SplitInstruction.prefix {n : ℕ} (I : SplitInstruction) (m : Ledger) (P : Prefix n) : (RatFunc ℚ)ˣ :=
  DyadicSplit.prefixFactor P I.coarse (fun j => match m.raws.reverse[j]? with
    | some (c,_) => I.coefficients c
    | none => 0)

def active (m : Ledger) : Option SplitInstruction :=
  match m.remaining with
  | c::cs => finalInstruction m c cs
  | [] => none

def dispatchUnit {n : ℕ} (m : Ledger) (P : Prefix n) (B : Batch) (sites : Table B.assigned.primes)
    (j : B.indices) (b : Bool) : ℤ_[B.primeAt j]ˣ := by
  classical
  exact match active m with
  | none => 1
  | some I =>
    if h : B.primeAt j ∣ I.task.modulus ∧
      ‖DyadicSplit.branchValue (siteAt B sites j) b (I.prefix m P : RatFunc ℚ)‖ =
        (if I.first (B.primeAt j) then ‖DyadicSplit.branchValue (siteAt B sites j) b I.task.element‖ else 1)
    then splitUnit _ _ _ _ _ (I.prefix m P).ne_zero h.2 else 1

def dispatchPrecision (m : Ledger) (B : Batch) (j : B.indices) (b : Bool) : ℕ :=
  match active m with
  | none => 0
  | some I => splitPrecision B I.task.modulus (fun _ _ => 0) j b

/-- Numerator, denominator and scalar normalizations of the task under
preparation. Processing the guard cutoff for these polynomials also makes its
rational scalar a unit at each subsequently assigned rational prime. -/
def taskGuardData (m : Ledger) : Finset ℚ[X] :=
  let x := (taskAt m.rounds).element
  {x.num, x.denom, C x.num.leadingCoeff, C x.denom.leadingCoeff}

/-- The ordinary logarithmic base also processes the guard threshold for every
factor being frozen at this raw. -/
def dispatcher (choose : Planner) : Driver where
  request := dispatch choose
  base m P := FrozenGuards.base (m.frozen ∪ freezeList m P ∪ taskGuardData m) P
  unit m P _ := dispatchUnit m P
  precision m _ _ B _ := dispatchPrecision m B

theorem dispatch_open_fibres {n : ℕ} (choose : Planner) (m : Ledger) (P : Prefix n)
    (T : Table P.state.assignment.primes) (h : m.remaining = []) :
    (dispatch choose m P T).toFreshFibres =
      (choose m P T).fibres.coverPrimes (FreshFibres.modulusPrimes (taskAt m.rounds).modulus) := by
  unfold dispatch
  split
  · rfl
  · rename_i c cs he; simp [h] at he

theorem dispatch_interior_roles {n : ℕ} (choose : Planner) (m : Ledger) (P : Prefix n)
    (T : Table P.state.assignment.primes) (h : m.remaining ≠ []) :
    let r := dispatch choose m P T
    r.freeze = ∅ ∧ ∀ p hp, r.role p hp = none := by
  unfold dispatch
  split
  · contradiction
  · refine ⟨rfl,fun p hp => ?_⟩
    exact ((FreshFibres.empty m P).coverPrimes_extra (pendingPrimes m) p hp (Finset.notMem_empty p)).1

theorem dispatcher_open {n : ℕ} (choose : Planner) (m : Ledger) (P : Prefix n)
    (T : Table P.state.assignment.primes) (h : m.remaining = []) :
    (dispatch choose m P T).openBlock = (choose m P T).block.columns ∧
    (dispatch choose m P T).width = (choose m P T).block.width ∧
    (dispatch choose m P T).freeze = freezeList m P ∧
    (dispatch choose m P T).install = (choose m P T).instruction := by
  have eqn : dispatch choose m P T = prepare (choose m P T) h := by
    unfold dispatch
    split
    · rfl
    · rename_i c cs he; simp [h] at he
  simp [eqn,prepare]

theorem dispatcher_calendar (choose : Planner) (r : ℕ) :
    let D := dispatcher choose
    D.openingFreeze (D.opening r) ∅ = (D.actualRequest (D.opening r)).freeze := by
  intro D
  exact (dispatcher_open choose _ _ _ (D.opening_empty r)).2.2.1.symm

theorem dispatcher_every_horizontal (choose : Planner) (f : Horizontal) :
    let D := dispatcher choose
    (∃ j, (chain D.requirements).raw j = f.val) ∨
      ∃ n, f.val ∈ (D.actualRequest n).freeze ∧ f.val ∉ Set.range (chain D.requirements).raw :=
  (dispatcher choose).horizontal_decided (fun _ => ∅) (fun r => (dispatcher_calendar choose r).subset) f

end UnconditionalCounterexample.Variations.DyadicLedger
