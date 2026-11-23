import UnconditionalCounterexample.Variations.DyadicDispatchEmission

/-!
# Execution of the saved split at the last raw of its round

The instruction installed at an opening survives each interior slot. It is
executed exactly at its designated final balanced raw, when the pending task
is removed. At that same raw the dispatcher's units and precisions give the
reserved target table on every fibre of its modulus.
-/

noncomputable section
namespace UnconditionalCounterexample.Variations.DyadicLedger

open GuardSupport Univariate RecursivePrefix CombinedGuardStep PrimaryChoices

private theorem open_queue {n : ℕ} (choose : Planner) (m : Ledger) (P : Prefix n)
    (T : Table P.state.assignment.primes) (h : m.remaining = []) :
    (dispatch choose m P T).reserve = false ∧
    (dispatch choose m P T).enqueue = ((choose m P T).instruction.map SplitInstruction.task).toList := by
  unfold dispatch
  split
  · exact ⟨rfl,rfl⟩
  · rename_i c cs he
    simp [h] at he

private theorem interior_queue {n : ℕ} (choose : Planner) (m : Ledger) (P : Prefix n)
    (T : Table P.state.assignment.primes) {c : RawColumn} {cs : List RawColumn}
    (h : m.remaining = c :: cs) : (dispatch choose m P T).enqueue = [] ∧
    (dispatch choose m P T).reserve = (finalInstruction m c cs).isSome := by
  unfold dispatch
  split
  · rename_i he; simp [h] at he
  · rename_i c' cs' he
    obtain ⟨rfl,rfl⟩ := List.cons.inj (he.symm.trans h)
    exact ⟨rfl,rfl⟩

private theorem active_none_of_empty (D : Driver) (n : ℕ) (h : (D.state n).remaining = []) :
    (D.state n).activeSplit = none := by
  cases n with
  | zero => rfl
  | succ n =>
    rw [D.state_succ] at h ⊢
    change ((D.state n).remaining ++ (D.actualRequest n).openBlock).tail = [] at h
    simp [Request.update,h]

private theorem hold_until_last (choose : Planner) (n : ℕ) (pre : List RawColumn) (c : RawColumn)
    (h : ((dispatcher choose).state n).remaining = pre ++ [c]) :
    let D := dispatcher choose
    (D.state (n+pre.length)).remaining = [c] ∧
    (D.state (n+pre.length)).activeSplit = (D.state n).activeSplit ∧
    (D.state (n+pre.length)).pending = (D.state n).pending := by
  let D := dispatcher choose
  induction pre generalizing n with
  | nil => simpa using h
  | cons a pre ih =>
    have hh : (D.state n).remaining = a :: (pre ++ [c]) := h
    have ne : (D.state n).remaining ≠ [] := by simp [hh]
    have op := ((D.actualRequest n).keep_block ne).1
    have ins := (D.actualRequest n).install_open ne
    have eq := interior_queue choose (D.state n) _ (table D.requirements n) hh
    change (D.actualRequest n).enqueue = [] ∧ (D.actualRequest n).reserve = _ at eq
    have no : (D.actualRequest n).reserve = false := by
      rw [eq.2]
      cases hopt : (D.state n).activeSplit <;> simp [finalInstruction,hopt]
    have tail := (D.column_of_pending hh).2.1
    have act : (D.state (n+1)).activeSplit = (D.state n).activeSplit := by
      rw [D.state_succ]
      simp [Request.update,hh,op,ins]
    have pend : (D.state (n+1)).pending = (D.state n).pending := by
      rw [D.state_succ]
      simp [Request.update,no,eq.1]
    have ht := ih (n+1) tail
    dsimp only at ht ⊢
    have hn : n + (a::pre).length = n+1+pre.length := by simp; omega
    rw [hn]
    exact ⟨ht.1,ht.2.1.trans act,ht.2.2.trans pend⟩

/-- The final stage carries exactly the instruction and task installed at
its opening, even when all intervening raws change the polynomial prefix. -/
theorem round_last_state (choose : Planner) (r : ℕ) :
    let D := dispatcher choose
    let o := openingData choose r
    let n := D.opening (r+1)-1
    (D.state n).remaining = [o.block.localColumn true o.block.reserved.val] ∧
      (D.state n).activeSplit = o.instruction ∧
      (D.state n).pending = (D.state (D.opening r)).pending ++ (o.instruction.map SplitInstruction.task).toList := by
  let D := dispatcher choose
  let o := openingData choose r
  let n := D.opening r
  let c := o.block.localColumn true o.block.reserved.val
  have emp : (D.state n).remaining = [] := D.opening_empty r
  have ⟨op,_,_,ins⟩ := dispatcher_open choose (D.state n) _ (table D.requirements n) emp
  change (D.actualRequest n).openBlock = o.block.columns at op
  change (D.actualRequest n).install = o.instruction at ins
  obtain ⟨no,push⟩ := open_queue choose (D.state n) _ (table D.requirements n) emp
  change (D.actualRequest n).reserve = false at no
  change (D.actualRequest n).enqueue = _ at push
  have none := active_none_of_empty D n emp
  obtain ⟨l,hl⟩ := List.getLast?_eq_some_iff.mp o.block.columns_last
  change o.block.columns = l ++ [c] at hl
  cases l with
  | nil =>
    have hlen := o.block.length_columns
    rw [hl] at hlen
    simp only [List.nil_append,List.length_singleton] at hlen
    have := o.block.positive
    omega
  | cons a pre =>
    have tail : (D.state (n+1)).remaining = pre ++ [c] := by
      rw [D.state_succ]
      simp [Request.update,emp,op,hl]
    have act : (D.state (n+1)).activeSplit = o.instruction := by
      rw [D.state_succ]
      simp [Request.update,emp,op,hl,none,ins]
    have pend : (D.state (n+1)).pending = (D.state n).pending ++ (o.instruction.map SplitInstruction.task).toList := by
      rw [D.state_succ]
      simp [Request.update,no,push,o,n,D,openingData]
    have ht := hold_until_last choose (n+1) pre c tail
    have hn : D.opening (r+1)-1 = n+1+pre.length := by
      rw [D.next_opening]
      change n + (D.actualRequest n).openBlock.length -1 = _
      rw [op,hl]
      simp; omega
    dsimp only
    change (D.state (D.opening (r+1)-1)).remaining = [c] ∧ _
    rw [hn]
    exact ⟨ht.1,ht.2.1.trans act,ht.2.2.trans pend⟩

/-- After every completed block the dispatcher has drained its split queue. -/
theorem opening_no_pending (choose : Planner) (r : ℕ) :
    ((dispatcher choose).state ((dispatcher choose).opening r)).pending = [] := by
  let D := dispatcher choose
  induction r with
  | zero => rfl
  | succ r ih =>
    let o := openingData choose r
    let n := D.opening (r+1)-1
    let c := o.block.localColumn true o.block.reserved.val
    have ⟨hq,ha,hp⟩ := round_last_state choose r
    change (D.state n).remaining = [c] at hq
    change (D.state n).activeSplit = o.instruction at ha
    change (D.state n).pending = (D.state (D.opening r)).pending ++ _ at hp
    have ⟨en,he⟩ := interior_queue choose (D.state n) _ (table D.requirements n) hq
    change (D.actualRequest n).reserve = _ at he
    change (D.actualRequest n).enqueue = [] at en
    have hs : D.opening (r+1) = n+1 := by
      have h := D.opening_strict (Nat.lt_succ_self r)
      change D.opening r < D.opening (r+1) at h
      change D.opening (r+1) = D.opening (r+1)-1+1
      omega
    change (D.state (D.opening (r+1))).pending = []
    rw [hs,D.state_succ]
    change (D.state (D.opening r)).pending = [] at ih
    rw [ih,List.nil_append] at hp
    change (D.state n).pending = (o.instruction.map SplitInstruction.task).toList at hp
    cases hf : o.instruction with
    | none => simp [Request.update,en,hp,he,finalInstruction,ha,hf]
    | some I =>
      have hc := o.reserved_eq I hf
      change c = .balanced I.channel I.index at hc
      simp [Request.update,en,hp,he,finalInstruction,ha,hf,hc]

/-- The selected slot executes the round's named instruction, including
removal of the head task and its permanent reservation record. -/
theorem last_executes (choose : Planner) (r : ℕ) (I : SplitInstruction)
    (hi : (openingData choose r).instruction = some I) :
    let D := dispatcher choose
    let n := D.opening (r+1)-1
    active (D.state n) = some I ∧ (D.actualRequest n).reserve = true ∧
      ((D.state n).pending ++ (D.actualRequest n).enqueue).head? = some I.task ∧
      (D.actualRequest n).column = .balanced I.channel I.index := by
  let D := dispatcher choose
  let o := openingData choose r
  let n := D.opening (r+1)-1
  have ⟨hq,ha,hp⟩ := round_last_state choose r
  change (D.state n).remaining = _ at hq
  change (D.state n).activeSplit = _ at ha
  change (D.state n).pending = _ at hp
  rw [hi] at ha hp
  have hc := o.reserved_eq I hi
  rw [hc] at hq
  have ⟨en,hr⟩ := interior_queue choose (D.state n) _ (table D.requirements n) hq
  change (D.actualRequest n).reserve = _ at hr
  change (D.actualRequest n).enqueue = [] at en
  change active (D.state n) = some I ∧ (D.actualRequest n).reserve = true ∧
    ((D.state n).pending ++ (D.actualRequest n).enqueue).head? = some I.task ∧ _
  refine ⟨by simp [active,hq,finalInstruction,ha], by simpa [finalInstruction,ha] using hr, ?_, (D.column_of_pending hq).1⟩
  rw [hp,en,opening_no_pending]
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem selected_unit {n : ℕ} (m : Ledger) (P : Prefix n) (B : Batch) (sites : Table B.assigned.primes)
    (j : B.indices) (b : Bool) (I : SplitInstruction) (ha : active m = some I)
    (hp : B.primeAt j ∣ I.task.modulus) (h : ‖DyadicSplit.branchValue (siteAt B sites j) b (I.prefix m P : RatFunc ℚ)‖ =
      if I.first (B.primeAt j) then ‖DyadicSplit.branchValue (siteAt B sites j) b I.task.element‖ else 1) :
    (dispatchUnit m P B sites j b).val.val = DyadicSplit.reservedTarget (I.first (B.primeAt j))
      (DyadicSplit.branchValue (siteAt B sites j) b I.task.element)
      (DyadicSplit.branchValue (siteAt B sites j) b (I.prefix m P : RatFunc ℚ)) := by
  unfold dispatchUnit
  simp only [ha]
  rw [dite_eq_left (And.intro hp h)]
  exact splitUnit_value _ _ _ _ _ _ _

/-- Prefix valuation matching is the only arithmetic input to the actual
unit and precision prescriptions at the executed slot. -/
theorem last_targets (choose : Planner) (r : ℕ) (I : SplitInstruction)
    (hi : (openingData choose r).instruction = some I) (hx : I.task.element ≠ 0) :
    (let D := dispatcher choose; let n := D.opening (r+1)-1;
      ∀ j : (selection D.requirements n).batch.indices, (primes j.val).val ∣ I.task.modulus →
        (D.actualRequest n).column.atPrimary (primes j.val) ((D.actualRequest n).nextRole (primes j.val)) = 0) →
    (let D := dispatcher choose; let n := D.opening (r+1)-1; let P := (chain D.requirements).approx n;
      ∀ j : (selection D.requirements n).batch.indices, (primes j.val).val ∣ I.task.modulus → ∀ b,
        ‖DyadicSplit.branchValue (selectionSite D.requirements n j) b (I.prefix (D.state n) P : RatFunc ℚ)‖ =
        if I.first (primes j.val).val then ‖DyadicSplit.branchValue (selectionSite D.requirements n j) b I.task.element‖ else 1) →
    let D := dispatcher choose; let n := D.opening (r+1)-1; let P := (chain D.requirements).approx n
    actualTargets D.requirements n = DyadicSplit.reserveTargets _ _ (actualTargets D.requirements n)
      I.task.modulus I.first I.task.element (I.prefix (D.state n) P : RatFunc ℚ) hx (I.prefix _ _).ne_zero := by
  intro hz hm
  let D := dispatcher choose
  let n := D.opening (r+1)-1
  let P := (chain D.requirements).approx n
  let B := (selection D.requirements n).batch
  have ha : active (D.state n) = some I := (last_executes choose r I hi).1
  apply D.actualTargets_eq_reserved n _ _ _ _ hx _ hz
  · intro j hp b
    change (dispatchUnit (D.state n) P B (table D.requirements (n+1)) j b).val.val = _
    have h := hm j hp b
    exact selected_unit _ _ _ _ _ _ I ha hp h
  · intro j hp b
    change dispatchPrecision (D.state n) B j b = _
    unfold dispatchPrecision
    change B.primeAt j ∣ I.task.modulus at hp
    simp only [ha,splitPrecision,ite_eq_left hp]
    rfl

end UnconditionalCounterexample.Variations.DyadicLedger
