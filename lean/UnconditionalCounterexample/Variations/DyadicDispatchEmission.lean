import UnconditionalCounterexample.Variations.DyadicEmission
import UnconditionalCounterexample.Variations.DyadicDispatch

/-!
# The dispatcher’s raw stages and their labelled columns

Every opening of the dispatcher instantiates the block emission theorem.
When its auxiliary list records exactly the newly requested auxiliary roles
without repetitions, distinct raw stages have distinct labelled columns.
-/

noncomputable section
namespace UnconditionalCounterexample.Variations.DyadicLedger

open GuardSupport Univariate DyadicEscape

def openingData (choose : Planner) (r : ℕ) :=
  let D := dispatcher choose
  let n := D.opening r
  choose (D.state n) ((chain D.requirements).approx n) (table D.requirements n)

def dispatcherEmission (choose : Planner) : Emission (dispatcher choose) where
  block r := (openingData choose r).block
  opened r := (dispatcher_open choose _ _ _ ((dispatcher choose).opening_empty r)).1
  start r := (openingData choose r).start_eq
  width r := (dispatcher_open choose _ _ _ ((dispatcher choose).opening_empty r)).2.1.symm

namespace Emission
variable {D : Driver} (E : Emission D)

/-- These two checks are finite checks on the actual data at each opening. -/
structure Recorded : Prop where
  nodup : ∀ r, (E.block r).auxiliary.Nodup
  allocated : ∀ r (c : RawColumn), c ∈ (E.block r).auxiliary →
    ∃ p : PrimeIndex, ∃ k i e, ∃ hp : p ∈ (D.actualRequest (D.opening r)).births.primes,
      c = .auxiliary p k i e ∧ (D.actualRequest (D.opening r)).role p hp = some (.auxiliary k i e)

variable (h : E.Recorded)

include h in
private theorem different_kind (r : ℕ) (i : Fin (E.block r).auxiliary.length) (g : Generator) :
    (E.block r).auxiliary[i.val] ≠ regularColumn g := by
  obtain ⟨_, _, _, _, _, he, _⟩ := h.allocated r _ (List.getElem_mem (h := i.isLt))
  rw [he]
  cases g <;> intro hn <;> cases hn

include h in
private theorem same_slot {r s : ℕ} (i : Fin (E.block r).auxiliary.length)
    (j : Fin (E.block s).auxiliary.length) (eq : (E.block r).auxiliary[i.val] = (E.block s).auxiliary[j.val]) :
    E.rounds.auxiliaryStage r i = E.rounds.auxiliaryStage s j := by
  obtain ⟨p,k,t,e,hp,hr,_⟩ := h.allocated r _ (List.getElem_mem (h := i.isLt))
  obtain ⟨q,l,u,d,hq,hs,_⟩ := h.allocated s _ (List.getElem_mem (h := j.isLt))
  have he := hr.symm.trans (eq.trans hs)
  obtain rfl := (RawColumn.auxiliary.inj he).1
  have hr := D.opening_strict.injective (D.schedule.requested_unique hp hq)
  subst s
  obtain rfl := Fin.ext ((h.nodup r).eq_of_getElem_eq i.isLt j.isLt eq)
  rfl

private theorem regularColumn_injective : Function.Injective regularColumn := by
  intro a b he
  cases a <;> cases b <;> cases he <;> rfl

include E h in
/-- There is one raw for each indicated column. The proof uses birth
freshness for distinct rounds' auxiliary primes. -/
theorem column_injective : Function.Injective (fun n => (D.actualRequest n).column) := by
  intro n m he
  rcases E.exhaustive n with ⟨r,i,hi,hc⟩ | ⟨g,hg,hc⟩ <;>
    rcases E.exhaustive m with ⟨s,j,hj,hd⟩ | ⟨a,ha,hd⟩
  · exact hi.symm.trans ((E.same_slot h i j (hc.symm.trans (he.trans hd))).trans hj)
  · exact False.elim (E.different_kind h r i a (hc.symm.trans (he.trans hd)))
  · exact False.elim (E.different_kind h s j g (hd.symm.trans (he.symm.trans hc)))
  · have eg := regularColumn_injective (hc.symm.trans (he.trans hd))
    exact hg.symm.trans ((congrArg E.rounds.regularStage eg).trans ha)

include h in
theorem regular_iff (n : ℕ) (g : Generator) :
    (D.actualRequest n).column = regularColumn g ↔ E.rounds.regularStage g = n :=
  ⟨fun hc => E.column_injective h ((E.regular g).trans hc.symm), fun he => he ▸ E.regular g⟩

/-- The reserved raw is the actual final column, immediately before the
next opening of the same dispatcher. -/
theorem reserved_final (r : ℕ) :
    ∃ k i, i < (E.block r).width ∧ DyadicBlocks.Rounds.code k i = (E.block r).reserved.val ∧
      E.rounds.regularStage (.balanced k ((E.block r).start+i)) + 1 = D.opening (r+1) ∧
      (D.actualRequest (D.opening (r+1)-1)).column = .balanced k ((E.block r).start+i) := by
  obtain ⟨k,i,hi,hc,hs⟩ := E.rounds.exists_reserved_last r
  rw [E.index_boundary,E.stage_boundary] at hs
  refine ⟨k,i,hi,hc,hs,?_⟩
  rw [← hs,Nat.add_sub_cancel]
  exact E.regular _

end Emission
end UnconditionalCounterexample.Variations.DyadicLedger
