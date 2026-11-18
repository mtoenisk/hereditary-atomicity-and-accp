import UnconditionalCounterexample.CombinedGuardStep
import UnconditionalCounterexample.RawWords
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.Tuple.Basic

/-!
# Concrete raw prefixes and their common infinite sequence

A prefix stores actual rational raw polynomials, their normalization exponents,
and the exact combined guard batches used to select them. Structural invariants
record monicity, irreducibility, nonzero constants, increasing degrees, support
in each polynomial's own ordinary processing set, and the exponential degree
budget in the current cutoff. `Next.append` preserves all earlier data.

Primitive recursion from a supplied successor yields unique consistent global
raw, exponent, and batch sequences. The guard projection uses completed
prefix `n+1` as assignment `n`, so the first nonempty batch has birth zero.
There is no independent guard recursion and no off-by-one arithmetic-stage
identification: raw stage n uses paper precision n+1.

This module proves structural recursion and its invariants. It neither assumes
nor proves all local arithmetic and geometric conclusions of Proposition 3.1. The concrete
stage selection supplies those proofs
for the same choices used by the successor operation.
-/

noncomputable section
namespace UnconditionalCounterexample.RecursivePrefix
open Polynomial GuardSupport CombinedGuardStep

/-- Actual selected data before the next raw polynomial is chosen. -/
structure Prefix (n : ℕ) where
  raw : Fin n → ℚ[X]
  exponent : Fin n → ℕ
  batch : Fin n → Batch
  state : State
  monic : ∀ j, (raw j).Monic
  irreducible : ∀ j, Irreducible (raw j)
  constant_ne_zero : ∀ j, (raw j).coeff 0 ≠ 0
  degree_five : ∀ j, 5 ≤ (raw j).natDegree
  exponent_pos : ∀ j, 0 < exponent j
  degree_strict : StrictMono (fun j => (raw j).natDegree)
  batch_stage : ∀ j, (batch j).stage = j.val
  raw_support : ∀ j k (p : PrimeIndex), p.val ∣ ((raw j).coeff k).den →
    p ∈ (batch j).processed.primes
  assigned_subset : ∀ j, (batch j).assigned.primes ⊆ state.assignment.primes
  stage_cutoff : n ≤ state.cutoff
  degree_budget : n = 0 ∨ 2 ^ (4 + ∑ j, (raw j).natDegree) ≤ state.cutoff

def empty : Prefix 0 where
  raw := Fin.elim0
  exponent := Fin.elim0
  batch := Fin.elim0
  state := zeroState
  monic := fun j => Fin.elim0 j
  irreducible := fun j => Fin.elim0 j
  constant_ne_zero := fun j => Fin.elim0 j
  degree_five := fun j => Fin.elim0 j
  exponent_pos := fun j => Fin.elim0 j
  degree_strict := fun i => Fin.elim0 i
  batch_stage := fun j => Fin.elim0 j
  raw_support := fun j => Fin.elim0 j
  assigned_subset := fun j => Fin.elim0 j
  stage_cutoff := le_rfl
  degree_budget := Or.inl rfl

/-- One selected polynomial and its actual processing batch. These are
structural selection outputs, not an assumption of the construction theorem. -/
structure Next {n : ℕ} (P : Prefix n) where
  raw : ℚ[X]
  exponent : ℕ
  batch : Batch
  monic : raw.Monic
  irreducible : Irreducible raw
  constant_ne_zero : raw.coeff 0 ≠ 0
  degree_five : 5 ≤ raw.natDegree
  exponent_pos : 0 < exponent
  degree_gt : ∀ j, (P.raw j).natDegree < raw.natDegree
  batch_stage : batch.stage = n
  raw_support : ∀ k (p : PrimeIndex), p.val ∣ (raw.coeff k).den →
    p ∈ batch.processed.primes
  assigned_subset : P.state.assignment.primes ⊆ batch.assigned.primes
  guard_persistent : ∀ p (hp : p ∈ P.state.assignment.primes) (hp' : p ∈ batch.assigned.primes),
    batch.assigned.guard p hp' = P.state.assignment.guard p hp
  new_birth : ∀ p (hp : p ∈ batch.assigned.primes), p ∉ P.state.assignment.primes →
    (batch.assigned.guard p hp).birth = n
  cutoff_gt : P.state.cutoff < batch.cutoff
  stage_cutoff : n + 1 ≤ batch.cutoff
  degree_budget : 2 ^ (4 + (∑ j, (P.raw j).natDegree) + raw.natDegree) ≤ batch.cutoff

namespace Next
variable {n : ℕ} {P : Prefix n} (S : Next P)

def append : Prefix (n + 1) where
  raw := Fin.snoc P.raw S.raw
  exponent := Fin.snoc P.exponent S.exponent
  batch := Fin.snoc P.batch S.batch
  state := S.batch.toState
  monic := Fin.lastCases (by simpa using S.monic) (fun j => by simpa using P.monic j)
  irreducible := Fin.lastCases (by simpa using S.irreducible) (fun j => by simpa using P.irreducible j)
  constant_ne_zero := Fin.lastCases (by simpa using S.constant_ne_zero)
    (fun j => by simpa using P.constant_ne_zero j)
  degree_five := Fin.lastCases (by simpa using S.degree_five) (fun j => by simpa using P.degree_five j)
  exponent_pos := Fin.lastCases (by simpa using S.exponent_pos) (fun j => by simpa using P.exponent_pos j)
  degree_strict := by
    intro i j hij
    cases i using Fin.lastCases with
    | last => exact False.elim ((not_lt_of_ge (Fin.le_last j)) hij)
    | cast i =>
      cases j using Fin.lastCases with
      | last => simpa only [Fin.snoc_castSucc, Fin.snoc_last] using S.degree_gt i
      | cast j =>
        simpa only [Fin.snoc_castSucc] using P.degree_strict (show i < j from hij)
  batch_stage := Fin.lastCases (by simpa using S.batch_stage) (fun j => by simpa using P.batch_stage j)
  raw_support := Fin.lastCases (by simpa using S.raw_support) (fun j => by simpa using P.raw_support j)
  assigned_subset := Fin.lastCases (by simpa only [Fin.snoc_last, Batch.toState] using (Finset.Subset.refl S.batch.assigned.primes))
    (fun j => by simpa only [Fin.snoc_castSucc, Batch.toState] using (P.assigned_subset j).trans S.assigned_subset)
  stage_cutoff := S.stage_cutoff
  degree_budget := Or.inr (by
    simpa only [Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last, add_assoc, Batch.toState] using S.degree_budget)

@[simp] theorem append_raw_old (j : Fin n) : S.append.raw j.castSucc = P.raw j := by simp only [append, Fin.snoc_castSucc]
@[simp] theorem append_exponent_old (j : Fin n) : S.append.exponent j.castSucc = P.exponent j := by simp only [append, Fin.snoc_castSucc]
@[simp] theorem append_batch_old (j : Fin n) : S.append.batch j.castSucc = P.batch j := by simp only [append, Fin.snoc_castSucc]
@[simp] theorem append_raw_last : S.append.raw (Fin.last n) = S.raw := by simp only [append, Fin.snoc_last]
@[simp] theorem append_exponent_last : S.append.exponent (Fin.last n) = S.exponent := by simp only [append, Fin.snoc_last]
@[simp] theorem append_batch_last : S.append.batch (Fin.last n) = S.batch := by simp only [append, Fin.snoc_last]
@[simp] theorem append_state : S.append.state = S.batch.toState := rfl

theorem append_degree_sum :
    (∑ j, (S.append.raw j).natDegree) = (∑ j, (P.raw j).natDegree) + S.raw.natDegree := by
  simp only [append, Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last]

end Next

/-- Every stored denominator is supported on the current actual assignment. -/
theorem Prefix.current_support {n : ℕ} (P : Prefix n) (j : Fin n) (k : ℕ)
    (p : PrimeIndex) (hp : p.val ∣ ((P.raw j).coeff k).den) : p ∈ P.state.assignment.primes :=
  P.assigned_subset j ((P.batch j).processed_subset_assigned (P.raw_support j k p hp))

theorem Prefix.current_degree_budget {n : ℕ} (P : Prefix n) (hn : n ≠ 0) :
    2 ^ (4 + ∑ j, (P.raw j).natDegree) ≤ P.state.cutoff :=
  P.degree_budget.resolve_left hn

/-- Total raw family used by the literal finite-word API; the unused tail is one. -/
def Prefix.rawAt {n : ℕ} (P : Prefix n) (j : ℕ) : ℚ[X] :=
  if h : j < n then P.raw ⟨j, h⟩ else 1

/-- Total exponent family used by the literal finite-word API; the unused tail is zero. -/
def Prefix.exponentAt {n : ℕ} (P : Prefix n) (j : ℕ) : ℕ :=
  if h : j < n then P.exponent ⟨j, h⟩ else 0

@[simp] theorem Prefix.rawAt_lt {n : ℕ} (P : Prefix n) (j : ℕ) (hj : j < n) :
    P.rawAt j = P.raw ⟨j, hj⟩ := by simp only [Prefix.rawAt, dite_eq_left hj]

@[simp] theorem Prefix.exponentAt_lt {n : ℕ} (P : Prefix n) (j : ℕ) (hj : j < n) :
    P.exponentAt j = P.exponent ⟨j, hj⟩ := by simp only [Prefix.exponentAt, dite_eq_left hj]

theorem Prefix.rawAt_monic {n : ℕ} (P : Prefix n) (j : ℕ) (hj : j < n) :
    (P.rawAt j).Monic := by rw [P.rawAt_lt j hj]; exact P.monic _

variable {A : Type*}

def globalValue (q : ∀ n : ℕ, Fin n → A) (k : ℕ) : A :=
  q (k + 1) (Fin.last k)

theorem prefix_persistent (q : ∀ n : ℕ, Fin n → A)
    (hq : ∀ n (j : Fin n), q (n + 1) j.castSucc = q n j)
    {m n : ℕ} (hmn : m ≤ n) (j : Fin m) :
    q n (Fin.castLE hmn j) = q m j := by
  induction n, hmn using Nat.le_induction with
  | base => rfl
  | succ n hmn ih =>
    exact (hq n (Fin.castLE hmn j)).trans ih

theorem prefix_agrees_globalValue (q : ∀ n : ℕ, Fin n → A)
    (hq : ∀ n (j : Fin n), q (n + 1) j.castSucc = q n j)
    (n : ℕ) (j : Fin n) : q n j = globalValue q j.val := by
  exact prefix_persistent q hq (Nat.succ_le_iff.mpr j.is_lt) (Fin.last j.val)

theorem globalValue_unique (q : ∀ n : ℕ, Fin n → A) (f : ℕ → A)
    (hf : ∀ n (j : Fin n), q n j = f j.val) : f = globalValue q := by
  funext k
  exact (hf (k + 1) (Fin.last k)).symm

theorem existsUnique_globalValue (q : ∀ n : ℕ, Fin n → A)
    (hq : ∀ n (j : Fin n), q (n + 1) j.castSucc = q n j) :
    ∃! f : ℕ → A, ∀ n (j : Fin n), q n j = f j.val :=
  ⟨globalValue q, prefix_agrees_globalValue q hq,
    fun f hf => globalValue_unique q f hf⟩

theorem globalValue_of_snoc (q : ∀ n : ℕ, Fin n → A) (n : ℕ) (a : A)
    (hsnoc : q (n + 1) = Fin.snoc (q n) a) : globalValue q n = a := by
  simp only [globalValue, hsnoc, Fin.snoc_last]

theorem coherent_of_snoc (q : ∀ n : ℕ, Fin n → A) (a : ℕ → A)
    (hsnoc : ∀ n, q (n + 1) = Fin.snoc (q n) (a n)) :
    ∀ n (j : Fin n), q (n + 1) j.castSucc = q n j := by
  intro n j
  rw [hsnoc n, Fin.snoc_castSucc]

theorem globalValue_eq_of_snoc (q : ∀ n : ℕ, Fin n → A) (a : ℕ → A)
    (hsnoc : ∀ n, q (n + 1) = Fin.snoc (q n) (a n)) : globalValue q = a := by
  funext n
  exact globalValue_of_snoc q n (a n) (hsnoc n)

theorem successor_eq_snoc_globalValue (q : ∀ n : ℕ, Fin n → A)
    (hq : ∀ n (j : Fin n), q (n + 1) j.castSucc = q n j) (n : ℕ) :
    q (n + 1) = Fin.snoc (q n) (globalValue q n) := by
  have hinit : Fin.init (q (n + 1)) = q n := funext (hq n)
  rw [← hinit]
  exact (Fin.snoc_init_self (q (n + 1))).symm


/-- A single sequence of concrete structural append steps. -/
structure Chain where
  approx : ∀ n, Prefix n
  next : ∀ n, Next (approx n)
  initial : approx 0 = empty
  step : ∀ n, approx (n + 1) = (next n).append

/-- Primitive recursion on an actual structural successor operation. -/
def run (succ : ∀ n (P : Prefix n), Next P) : ∀ n, Prefix n
  | 0 => empty
  | n + 1 => (succ n (run succ n)).append

def Chain.ofSuccessor (succ : ∀ n (P : Prefix n), Next P) : Chain where
  approx := run succ
  next n := succ n (run succ n)
  initial := rfl
  step _ := rfl

theorem chain_nonempty_of_successor
    (hsucc : ∀ n (P : Prefix n), Nonempty (Next P)) : Nonempty Chain :=
  ⟨Chain.ofSuccessor (fun n P => Classical.choice (hsucc n P))⟩

namespace Chain
variable (C : Chain)

theorem raw_coherent (n : ℕ) (j : Fin n) :
    (C.approx (n + 1)).raw j.castSucc = (C.approx n).raw j := by
  rw [C.step]
  exact (C.next n).append_raw_old j

theorem exponent_coherent (n : ℕ) (j : Fin n) :
    (C.approx (n + 1)).exponent j.castSucc = (C.approx n).exponent j := by
  rw [C.step]
  exact (C.next n).append_exponent_old j

theorem batch_coherent (n : ℕ) (j : Fin n) :
    (C.approx (n + 1)).batch j.castSucc = (C.approx n).batch j := by
  rw [C.step]
  exact (C.next n).append_batch_old j

def raw : ℕ → ℚ[X] := globalValue (fun n => (C.approx n).raw)
def exponent : ℕ → ℕ := globalValue (fun n => (C.approx n).exponent)
def batch : ℕ → Batch := globalValue (fun n => (C.approx n).batch)

theorem raw_agrees (n : ℕ) (j : Fin n) : (C.approx n).raw j = C.raw j.val :=
  prefix_agrees_globalValue (fun m => (C.approx m).raw) C.raw_coherent n j

theorem exponent_agrees (n : ℕ) (j : Fin n) : (C.approx n).exponent j = C.exponent j.val :=
  prefix_agrees_globalValue (fun m => (C.approx m).exponent) C.exponent_coherent n j

theorem batch_agrees (n : ℕ) (j : Fin n) : (C.approx n).batch j = C.batch j.val :=
  prefix_agrees_globalValue (fun m => (C.approx m).batch) C.batch_coherent n j

theorem rawAt_agrees (n j : ℕ) (hj : j < n) : (C.approx n).rawAt j = C.raw j := by
  rw [Prefix.rawAt_lt _ j hj, C.raw_agrees]

theorem exponentAt_agrees (n j : ℕ) (hj : j < n) :
    (C.approx n).exponentAt j = C.exponent j := by
  rw [Prefix.exponentAt_lt _ j hj, C.exponent_agrees]

theorem existsUnique_raw : ∃! F : ℕ → ℚ[X], ∀ n (j : Fin n), (C.approx n).raw j = F j.val :=
  existsUnique_globalValue (fun n => (C.approx n).raw) C.raw_coherent

theorem existsUnique_exponent : ∃! E : ℕ → ℕ, ∀ n (j : Fin n), (C.approx n).exponent j = E j.val :=
  existsUnique_globalValue (fun n => (C.approx n).exponent) C.exponent_coherent

theorem raw_eq_selected (n : ℕ) : C.raw n = (C.next n).raw := by
  simp only [raw, globalValue, C.step, Next.append_raw_last]

theorem exponent_eq_selected (n : ℕ) : C.exponent n = (C.next n).exponent := by
  simp only [exponent, globalValue, C.step, Next.append_exponent_last]

theorem batch_eq_selected (n : ℕ) : C.batch n = (C.next n).batch := by
  simp only [batch, globalValue, C.step, Next.append_batch_last]

theorem raw_monic (n : ℕ) : (C.raw n).Monic := (C.approx (n + 1)).monic (Fin.last n)
theorem raw_irreducible (n : ℕ) : Irreducible (C.raw n) := (C.approx (n + 1)).irreducible (Fin.last n)
theorem raw_constant_ne_zero (n : ℕ) : (C.raw n).coeff 0 ≠ 0 :=
  (C.approx (n + 1)).constant_ne_zero (Fin.last n)
theorem raw_degree_five (n : ℕ) : 5 ≤ (C.raw n).natDegree :=
  (C.approx (n + 1)).degree_five (Fin.last n)
theorem exponent_pos (n : ℕ) : 0 < C.exponent n := (C.approx (n + 1)).exponent_pos (Fin.last n)
theorem batch_stage (n : ℕ) : (C.batch n).stage = n := (C.approx (n + 1)).batch_stage (Fin.last n)

theorem raw_degree_strict : StrictMono (fun n => (C.raw n).natDegree) := by
  intro i j hij
  have hfin : (⟨i, by omega⟩ : Fin (j + 1)) < Fin.last j := hij
  have h := (C.approx (j + 1)).degree_strict hfin
  simpa only [C.raw_agrees, Fin.val_last] using h

theorem raw_support (n k : ℕ) (p : PrimeIndex) (hp : p.val ∣ ((C.raw n).coeff k).den) :
    p ∈ (C.batch n).processed.primes :=
  (C.approx (n + 1)).raw_support (Fin.last n) k p hp

theorem state_assignment_eq_batch (n : ℕ) :
    (C.approx (n + 1)).state.assignment = (C.batch n).assigned := by
  rw [C.step n, C.batch_eq_selected n]
  rfl

/-- The guard projection has the same completed batches and the correct
birth clock; no independent guard recursion is introduced. -/
def guardChain : PaperGuardStages.ApproximationChain where
  assignments n := (C.approx (n + 1)).state.assignment
  increasing n := by
    rw [C.step (n + 1)]
    exact (C.next (n + 1)).assigned_subset
  persistent n p hp hp' := by
    revert hp'
    rw [C.step (n + 1)]
    intro hp'
    exact (C.next (n + 1)).guard_persistent p hp hp'
  initial_birth p hp := by
    revert hp
    rw [C.step 0]
    intro hp
    apply (C.next 0).new_birth p hp
    rw [C.initial]
    simp only [empty, zeroState, Finset.notMem_empty, not_false_eq_true]
  new_birth n p hp hn := by
    revert hp
    rw [C.step (n + 1)]
    intro hp
    exact (C.next (n + 1)).new_birth p hp hn
  covers n := by
    intro p hp
    apply (C.approx (n + 1)).state.covered
    apply (GuardStages.mem_primesThrough p _).mpr
    exact ((GuardStages.mem_primesThrough p n).mp hp).trans
      ((Nat.le_succ n).trans (C.approx (n + 1)).stage_cutoff)

theorem guardChain_assignments (n : ℕ) : C.guardChain.assignments n = (C.batch n).assigned :=
  C.state_assignment_eq_batch n

end Chain

end UnconditionalCounterexample.RecursivePrefix
