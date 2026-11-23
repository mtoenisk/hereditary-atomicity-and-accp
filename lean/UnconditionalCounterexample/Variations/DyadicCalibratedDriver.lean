import UnconditionalCounterexample.Variations.DyadicFrozenMass
import UnconditionalCounterexample.Variations.DyadicDispatch
import UnconditionalCounterexample.Variations.DyadicPermanentRoles

/-!
# A calibrated selector with actual weighted auxiliary and regular births

The auxiliary corrections are chosen from the actual prefix before the finite
layout is decided. All the required regular sites are then selected, the fair
freezing calendar is installed, and the resulting raw is emitted by the
univariate selection itself.
-/

noncomputable section
namespace UnconditionalCounterexample.Variations.DyadicLedger.Calibrated
open GuardSupport RecursivePrefix Univariate Polynomial FreezingCalendar OpeningCalibration

variable {n : ℕ}

private def known (m : Ledger) : Finset ℚ[X] := by
  classical exact m.frozen.filter fun f => f.Monic ∧ Irreducible f

private theorem known_horizontal (m : Ledger) : BulkInputs.HorizontalSet (known m) := by
  classical exact fun _ h => (Finset.mem_filter.mp h).2

private def next (m : Ledger) := candidates m.rounds ∅

private theorem next_horizontal (m : Ledger) : BulkInputs.HorizontalSet (next m) :=
  BulkInputs.candidates_horizontal _ (by simp [BulkInputs.HorizontalSet])

private def pending (m : Ledger) (P : Prefix n) := FreezingCalendar.pending P (known m) (next m)

private theorem pending_eq (m : Ledger) (P : Prefix n) : pending m P = freezeList m P := by
  classical
  ext f
  simp only [pending,freezeList,FreezingCalendar.pending,Finset.mem_filter,known,next,not_and]
  constructor
  · rintro ⟨hc,hn,hraw⟩
    exact ⟨hc,fun h => hn h (next_horizontal m f hc).1 (next_horizontal m f hc).2,hraw⟩
  · rintro ⟨hc,hn,hraw⟩
    exact ⟨hc,fun h => (hn h).elim,hraw⟩

private theorem pending_horizontal (m : Ledger) (P : Prefix n) : BulkInputs.HorizontalSet (pending m P) :=
  fun f h => next_horizontal m f (Finset.mem_filter.mp h).1

def phase (m : Ledger) (P : Prefix n) (T : Table P.state.assignment.primes) :=
  OpeningCalibration.select m P T (known m) (next m) (known_horizontal _) (next_horizontal _)
    (taskAt m.rounds).modulus m.regularBound

/-- Once the auxiliary prime labels have been chosen, specify the finite width,
reserved swap, and optional split word. -/
structure Layout (m : Ledger) (aux : List RawColumn) where
  block : Block
  start_eq : block.start = m.regularBound
  auxiliary_eq : block.auxiliary = aux
  instruction : Option SplitInstruction
  reserved_eq : ∀ I, instruction = some I →
    block.localColumn true block.reserved.val = .balanced I.channel I.index

abbrev Policy := ∀ {n}, (m : Ledger) → (P : Prefix n) → Table P.state.assignment.primes →
  (aux : List RawColumn) → Layout m aux

/-- Choosing one index per round gives a calibrated selector independently of
the split choice. -/
def unitWidth : Policy := fun m _ _ aux =>
  ⟨⟨m.regularBound,1,by decide,0,aux⟩,rfl,rfl,none,by simp⟩

def layout (policy : Policy) (m : Ledger) (P : Prefix n) (T : Table P.state.assignment.primes) :=
  policy m P T (columns (phase m P T))

def room (policy : Policy) (m : Ledger) (P : Prefix n) (T : Table P.state.assignment.primes) :=
  Classical.choice (finish (phase m P T) (layout policy m P T).block)

def planner (policy : Policy) : Planner := fun m P T =>
  { block := (layout policy m P T).block
    start_eq := (layout policy m P T).start_eq
    instruction := (layout policy m P T).instruction
    reserved_eq := (layout policy m P T).reserved_eq
    fibres := (room policy m P T).fibres }

abbrev driver (policy : Policy) : Driver := dispatcher (planner policy)
abbrev actualLayout (policy : Policy) (n : ℕ) := layout policy ((driver policy).state n)
  ((chain (driver policy).requirements).approx n) (table (driver policy).requirements n)
abbrev actualRoom (policy : Policy) (n : ℕ) := room policy ((driver policy).state n)
  ((chain (driver policy).requirements).approx n) (table (driver policy).requirements n)

theorem installed (policy : Policy) (t : ℕ) (h : ((driver policy).state t).remaining = []) :
    Installed (actualRoom policy t).fibres ((driver policy).actualRequest t).toFreshFibres := by
  rw [show ((driver policy).actualRequest t).toFreshFibres = _ from
    dispatch_open_fibres (planner policy) _ _ _ h]
  exact installed_coverPrimes _ _

/-- Every factor newly frozen at any actual raw attains the target mass, for
both channels, on that stage's actual permanent p-adic fibres. -/
theorem calibrated (policy : Policy) (n : ℕ) (f : ℚ[X]) (hf : f ∈ ((driver policy).actualRequest n).freeze)
    (k : Bool) : (driver policy).rationalMass (n+1) f (height f) k = height f k := by
  let D := driver policy
  by_cases h : (D.state n).remaining = []
  · have he := (dispatcher_open (planner policy) (D.state n) ((chain D.requirements).approx n) (table D.requirements n) h).2.2.1
    obtain hf' : f ∈ pending (D.state n) ((chain D.requirements).approx n) := by
      rw [pending_eq, ← he]
      exact hf
    exact (actualRoom policy n).mass_after D n (installed policy n h) ⟨f,hf'⟩ k
  · have he := (dispatch_interior_roles (planner policy) (D.state n) ((chain D.requirements).approx n) (table D.requirements n) h).1
    exact False.elim (Finset.notMem_empty f (he ▸ hf))

/-- Every monic irreducible is a raw or is retained and calibrated on both
channels of this same unconditional selection. -/
theorem selects (policy : Policy) (f : Horizontal) :
    let D := driver policy
    (∃ j, (chain D.requirements).raw j = f.val) ∨
      ∃ n, f.val ∉ Set.range (chain D.requirements).raw ∧
        ∀ k, D.rationalMass (n+1) f.val (height f.val) k = height f.val k := by
  intro D
  rcases dispatcher_every_horizontal (planner policy) f with h | ⟨n,hn,hr⟩
  · exact Or.inl h
  · exact Or.inr ⟨n,hr,calibrated policy n f.val hn⟩

/-- Each regular label needed by a column of the opening has an actual
permanent p-adic prime with that precise label. -/
theorem regular_covered (policy : Policy) (t : ℕ) (h : ((driver policy).state t).remaining = [])
    (l : RegularLabel) (hl : l ∈ (actualLayout policy t).block.required) :
    ∃! p, (driver policy).permanentRole p = some l.role := by
  let D := driver policy
  obtain ⟨p,hp⟩ : ∃ p, D.permanentRole p = some l.role := by
    rcases (actualRoom policy t).coverage l hl with ⟨p,hr⟩ | ⟨p,h,hr⟩
    · have ha : p ∈ D.assigned t := by
        by_contra hn
        rw [D.role_none_of_unassigned t p hn] at hr
        contradiction
      exact ⟨p,(D.role_eq_permanent p ha).symm.trans hr⟩
    · obtain ⟨hm,he,_⟩ := (installed policy t ‹_›).included p h
      exact ⟨p,(D.permanentRole_requested p hm).trans (he.trans hr)⟩
  exact ⟨p,hp,fun q hq => D.permanent_regular_unique hq hp⟩

/-- On every later selected raw, every newly labelled point gives precisely
the prescribed old horizontal orders. -/
theorem predicts (policy : Policy) (f : Horizontal) (n : ℕ) (hf : f.val ∈ ((driver policy).state n).frozen) :
    ((driver policy).actualRequest n).toFreshFibres.Predicts f := by
  classical
  let D := driver policy
  by_cases h : (D.state n).remaining = []
  · apply (actualRoom policy n).predicts_old _ (installed policy n h)
    exact Finset.mem_filter.mpr ⟨hf,f.property⟩
  · exact FreshFibres.predicts_of_unlabelled _
      (dispatch_interior_roles (planner policy) (D.state n) ((chain D.requirements).approx n)
        (table D.requirements n) h).2 f

theorem permanent_mass (policy : Policy) (f : Horizontal) {t b : ℕ}
    (hf : f.val ∈ ((driver policy).actualRequest t).freeze) (ht : t < b) (k : Bool) :
    (driver policy).rationalMass b f.val (height f.val) k = height f.val k :=
  (driver policy).frozen_mass t f hf (calibrated policy t f.val hf) (predicts policy f) ht k

end UnconditionalCounterexample.Variations.DyadicLedger.Calibrated
