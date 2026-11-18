import UnconditionalCounterexample.LogarithmicGuards
import UnconditionalCounterexample.GuardStages
import UnconditionalCounterexample.PrimaryChoices
import UnconditionalCounterexample.PairedDomain

/-!
# Permanent logarithmic guards from the common finite stages

The guards in Proposition 3.1 retain their representative
and first assignment stage. The finite initial batch may use any nonzero residue;
all positive-birth guards satisfy the paper's logarithmic interval. Finite choices
use monic integral models of earlier raws and the exponential degree cutoff.

The ordinary processing set and fresh auxiliary prime are separate: coefficients
use the ordinary set as denominator support, while the auxiliary guard is inserted
for permanent retention by later stages. Shifted-Eisenstein reduction makes the new
raw a unit at both auxiliary arguments whose residues differ from one.

`ApproximationChain` collects the guard assignments in the sequence of finite stages. From any such chain, first assignment gives a unique global guard,
finite initial birth sets, the manuscript finite-support theorem, and actual
paired Places with the fixed primary family. Integer localization then follows.

No integer-polynomial enumeration condition is used. The GuardStages import is
reused only for generic finite prime-set and fresh-prime helpers.
-/

namespace UnconditionalCounterexample.PaperGuardStages

open Polynomial GuardSupport GuardStages

/-- An actual permanently assigned paper guard, with a literal representative.
Only the finite birth-zero batch may violate the logarithmic interval. -/
structure Guard (p : PrimeIndex) where
  value : ℤ_[p.val]
  transcendental : Transcendental ℚ value.val
  unit : IsUnit value
  representative : ℕ
  residue : PadicInt.toZMod value = (representative : ZMod p.val)
  birth : ℕ
  logarithmic : 0 < birth → Nat.log 2 p.val ≤ representative ∧
    representative ≤ 2 * Nat.log 2 p.val

structure Assignment where
  primes : Finset PrimeIndex
  guard : (p : PrimeIndex) → p ∈ primes → Guard p

/-- The paper permits any nonzero residue at the finitely many initial primes. -/
theorem exists_initial_guard (p : PrimeIndex) :
    ∃ g : Guard p, g.birth = 0 ∧ g.representative = 1 := by
  obtain ⟨β, ht, hu, hr, _⟩ :=
    EvaluationChoices.exists_transcendental_unit_residue p.val 1 (by simp [p.property.ne_one])
  exact ⟨⟨β, ht, hu, 1, hr, 0, by omega⟩, rfl, rfl⟩

/-- At large new primes the paper's exact residue selection gives actual guards. -/
theorem exists_large_guard {J : Type*} (p : PrimeIndex) (i : ℕ)
    (I : Finset J) (F : J → ℤ_[p.val][X]) (hF : ∀ j ∈ I, (F j).Monic)
    (hp : 2 ^ (4 + ∑ j ∈ I, (F j).natDegree) < p.val) :
    ∃ g : Guard p, g.birth = i ∧ PadicInt.toZMod g.value ≠ 1 ∧
      ∀ j ∈ I, IsUnit ((F j).eval g.value) := by
  obtain ⟨w, β, hwlo, hwhi, _, _, ht, hu, hr, hr1, hraw⟩ :=
    LogarithmicGuards.exists_logarithmic_guard I F hF hp
  exact ⟨⟨β, ht, hu, w, hr, i, fun _ => ⟨hwlo, hwhi⟩⟩, rfl, hr1, hraw⟩

/-- Initialize a finite batch, including the small primes. -/
theorem exists_initial_assignment (S : Finset PrimeIndex) :
    ∃ A : Assignment, A.primes = S ∧ ∀ p (hp : p ∈ A.primes), (A.guard p hp).birth = 0 := by
  classical
  let g (p : PrimeIndex) := (exists_initial_guard p).choose
  exact ⟨⟨S, fun p _ => g p⟩, rfl, fun p _ => (exists_initial_guard p).choose_spec.1⟩

noncomputable def Assignment.extend (A : Assignment) (T : Finset PrimeIndex)
    (g : (p : PrimeIndex) → p ∈ T → p ∉ A.primes → Guard p) : Assignment := by
  classical
  exact ⟨T, fun p hp => if hold : p ∈ A.primes then A.guard p hold else g p hp hold⟩

@[simp] theorem Assignment.extend_primes (A : Assignment) (T : Finset PrimeIndex) (g) :
    (A.extend T g).primes = T := rfl

theorem Assignment.extend_old (A : Assignment) (T : Finset PrimeIndex) (g)
    (p : PrimeIndex) (hp : p ∈ A.primes) (hpT : p ∈ T) :
    (A.extend T g).guard p hpT = A.guard p hp := by
  simp only [Assignment.extend, dite_eq_left hp]

theorem Assignment.extend_new (A : Assignment) (T : Finset PrimeIndex) (g)
    (p : PrimeIndex) (hp : p ∉ A.primes) (hpT : p ∈ T) :
    (A.extend T g).guard p hpT = g p hpT hp := by
  simp only [Assignment.extend, dite_eq_right hp]

/-- Extend the same finite assignment at every newly requested large prime. -/
theorem exists_extension {J : Type*} (A : Assignment) (T : Finset PrimeIndex)
    (hAT : A.primes ⊆ T) (i : ℕ) (I : Finset J)
    (F : (p : PrimeIndex) → J → ℤ_[p.val][X])
    (hF : ∀ p ∈ T, p ∉ A.primes → ∀ j ∈ I, (F p j).Monic)
    (hlarge : ∀ p ∈ T, p ∉ A.primes → 2 ^ (4 + ∑ j ∈ I, (F p j).natDegree) < p.val) :
    ∃ B : Assignment, B.primes = T ∧ A.primes ⊆ B.primes ∧
      (∀ p (hp : p ∈ A.primes) (hpB : p ∈ B.primes), B.guard p hpB = A.guard p hp) ∧
      ∀ p (hp : p ∈ B.primes), p ∉ A.primes →
        (B.guard p hp).birth = i ∧ PadicInt.toZMod (B.guard p hp).value ≠ 1 ∧
        ∀ j ∈ I, IsUnit ((F p j).eval (B.guard p hp).value) := by
  classical
  have hex (p : PrimeIndex) (hp : p ∈ T) (hn : p ∉ A.primes) :=
    exists_large_guard p i I (F p) (hF p hp hn) (hlarge p hp hn)
  let g (p : PrimeIndex) (hp : p ∈ T) (hn : p ∉ A.primes) := (hex p hp hn).choose
  refine ⟨A.extend T g, rfl, hAT, ?_, ?_⟩
  · intro p hp hpB
    exact A.extend_old T g p hp hpB
  · intro p hp hn
    rw [A.extend_new T g p hn hp]
    exact (hex p hp hn).choose_spec

/-- Process a larger cutoff and all finitely many requested primary primes. -/
def nextPrimes (A : Assignment) (M : ℕ) (required : Finset PrimeIndex) : Finset PrimeIndex :=
  A.primes ∪ primesThrough M ∪ required

theorem subset_nextPrimes (A : Assignment) (M : ℕ) (required : Finset PrimeIndex) :
    A.primes ⊆ nextPrimes A M required := by
  intro p hp
  exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl hp)))

theorem cutoff_subset_nextPrimes (A : Assignment) (M : ℕ) (required : Finset PrimeIndex) :
    primesThrough M ⊆ nextPrimes A M required := by
  intro p hp
  exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inr hp)))

/-- Previous cutoff coverage gives the paper's exponential bound at each new
prime; no integer-polynomial enumeration is involved. -/
theorem large_of_unassigned (A : Assignment) (D : ℕ)
    (hcovered : primesThrough (2 ^ (4 + D)) ⊆ A.primes)
    (p : PrimeIndex) (hp : p ∉ A.primes) : 2 ^ (4 + D) < p.val := by
  by_contra hn
  exact hp (hcovered ((mem_primesThrough p _).mpr (by omega)))

/-- The ordinary guard component of a paper stage, with permanent old values. -/
theorem exists_stage_transition {J : Type*} (A : Assignment) (i D M : ℕ)
    (required : Finset PrimeIndex)
    (hcovered : primesThrough (2 ^ (4 + D)) ⊆ A.primes)
    (I : Finset J) (F : (p : PrimeIndex) → J → ℤ_[p.val][X])
    (hF : ∀ p ∉ A.primes, ∀ j ∈ I, (F p j).Monic)
    (hdegree : ∀ p ∉ A.primes, (∑ j ∈ I, (F p j).natDegree) ≤ D) :
    ∃ B : Assignment, B.primes = nextPrimes A M required ∧ A.primes ⊆ B.primes ∧
      (∀ p (hp : p ∈ A.primes) (hpB : p ∈ B.primes), B.guard p hpB = A.guard p hp) ∧
      ∀ p (hp : p ∈ B.primes), p ∉ A.primes →
        (B.guard p hp).birth = i ∧ PadicInt.toZMod (B.guard p hp).value ≠ 1 ∧
        ∀ j ∈ I, IsUnit ((F p j).eval (B.guard p hp).value) := by
  apply exists_extension A (nextPrimes A M required) (subset_nextPrimes A M required) i I F
  · intro p _ hn
    exact hF p hn
  · intro p _ hn
    have hdeg := hdegree p hn
    exact (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega :
      4 + (∑ j ∈ I, (F p j).natDegree) ≤ 4 + D)).trans_lt
      (large_of_unassigned A D hcovered p hn)

/-- Choose the paper's fresh auxiliary prime after ordinary prime processing. -/
theorem exists_fresh_auxiliary_guard {J : Type*} (A : Assignment) (i D M : ℕ)
    (I : Finset J) (F : (p : PrimeIndex) → J → ℤ_[p.val][X])
    (hF : ∀ p ∉ A.primes, ∀ j ∈ I, (F p j).Monic)
    (hdegree : ∀ p ∉ A.primes, (∑ j ∈ I, (F p j).natDegree) ≤ D) :
    ∃ ell : PrimeIndex, ∃ g : Guard ell, M < ell.val ∧ ell ∉ A.primes ∧
      g.birth = i ∧ PadicInt.toZMod g.value ≠ 1 ∧
      ∀ j ∈ I, IsUnit ((F ell j).eval g.value) := by
  obtain ⟨ell, hlarge, hfresh⟩ := GuardStages.exists_fresh_prime A.primes (max M (2 ^ (4 + D)))
  have hdeg := hdegree ell hfresh
  have hbound : 2 ^ (4 + ∑ j ∈ I, (F ell j).natDegree) < ell.val :=
    (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega :
      4 + (∑ j ∈ I, (F ell j).natDegree) ≤ 4 + D)).trans_lt
        ((le_max_right _ _).trans_lt hlarge)
  obtain ⟨g, hg, hr, hraw⟩ := exists_large_guard ell i I (F ell) (hF ell hfresh) hbound
  exact ⟨ell, g, (le_max_left _ _).trans_lt hlarge, hfresh, hg, hr, hraw⟩

/-- Insert the same auxiliary guard for permanent retention at later stages. -/
noncomputable def Assignment.insert (A : Assignment) (ell : PrimeIndex) (g : Guard ell) : Assignment := by
  classical
  exact A.extend (Insert.insert ell A.primes) fun p hp hn => by
    have heq : p = ell := (Finset.mem_insert.mp hp).resolve_right hn
    subst p
    exact g

@[simp] theorem Assignment.insert_primes (A : Assignment) (ell : PrimeIndex) (g : Guard ell) :
    (A.insert ell g).primes = Insert.insert ell A.primes := rfl

theorem Assignment.insert_old (A : Assignment) (ell : PrimeIndex) (g : Guard ell)
    (p : PrimeIndex) (hp : p ∈ A.primes) :
    (A.insert ell g).guard p (Finset.mem_insert_of_mem hp) = A.guard p hp := by
  apply Assignment.extend_old

theorem Assignment.insert_fresh (A : Assignment) (ell : PrimeIndex) (g : Guard ell)
    (hell : ell ∉ A.primes) :
    (A.insert ell g).guard ell (Finset.mem_insert_self ell A.primes) = g := by
  simp only [Assignment.insert, Assignment.extend, dite_eq_right hell]

/-- Reduction modulo p to the first power detects p-adic units as well. -/
theorem isUnit_iff_toZModPow_one_ne_zero {p : ℕ} [Fact p.Prime] (x : ℤ_[p]) :
    IsUnit x ↔ PadicInt.toZModPow 1 x ≠ 0 := by
  rw [← not_iff_not]
  simp only [not_not, ← RingHom.mem_ker, PadicInt.ker_toZModPow, pow_one,
    ← PadicInt.maximalIdeal_eq_span_p, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]

/-- The shifted-Eisenstein raw polynomial is a unit at every argument whose
residue differs from one, including the chosen primary and auxiliary guard. -/
theorem auxiliary_eval_unit {p : ℕ} [Fact p.Prime] (G : ℤ_[p][X]) (d : ℕ)
    (hG : G.map (PadicInt.toZModPow 1) = (X - C 1) ^ d)
    (β : ℤ_[p]) (hβ : PadicInt.toZMod β ≠ 1) : IsUnit (G.eval β) := by
  have hpprime : p.Prime := Fact.out
  let : Fact (p ^ 1).Prime := ⟨by simpa only [pow_one] using hpprime⟩
  apply (isUnit_iff_toZModPow_one_ne_zero _).mpr
  have heval := congrArg (Polynomial.eval (PadicInt.toZModPow 1 β)) hG
  simp only [eval_map, eval_pow, eval_sub, eval_X, eval_C, eval₂_at_apply] at heval
  rw [heval]
  apply pow_ne_zero
  have hsub : IsUnit (β - 1) := by
    apply (padicInt_isUnit_iff_toZMod_ne_zero _).mpr
    simpa only [map_sub, map_one, sub_ne_zero] using hβ
  simpa only [map_sub, map_one] using (isUnit_iff_toZModPow_one_ne_zero _).mp hsub

/-- The guard projection of the single simultaneous stage construction.
Coverage follows from its stage cutoffs being at least the stage number. -/
structure ApproximationChain where
  assignments : ℕ → Assignment
  increasing (n : ℕ) : (assignments n).primes ⊆ (assignments (n + 1)).primes
  persistent (n : ℕ) (p : PrimeIndex)
    (hp : p ∈ (assignments n).primes) (hp' : p ∈ (assignments (n + 1)).primes) :
    (assignments (n + 1)).guard p hp' = (assignments n).guard p hp
  initial_birth (p : PrimeIndex) (hp : p ∈ (assignments 0).primes) :
    ((assignments 0).guard p hp).birth = 0
  new_birth (n : ℕ) (p : PrimeIndex) (hp : p ∈ (assignments (n + 1)).primes)
    (hn : p ∉ (assignments n).primes) : ((assignments (n + 1)).guard p hp).birth = n + 1
  covers (n : ℕ) : primesThrough n ⊆ (assignments n).primes

namespace ApproximationChain

variable (C : ApproximationChain)

theorem monotone_primes : Monotone (fun n => (C.assignments n).primes) :=
  monotone_nat_of_le_succ C.increasing

/-- Every rational prime appears in a finite approximant. -/
theorem exhaustive (p : PrimeIndex) : ∃ n, p ∈ (C.assignments n).primes :=
  ⟨p.val, C.covers p.val ((mem_primesThrough p p.val).mpr le_rfl)⟩

/-- First assignment stage of a prime. -/
noncomputable def birth (p : PrimeIndex) : ℕ := Nat.find (C.exhaustive p)

theorem birth_mem (p : PrimeIndex) : p ∈ (C.assignments (C.birth p)).primes :=
  Nat.find_spec (C.exhaustive p)

theorem not_mem_before_birth (p : PrimeIndex) {n : ℕ} (hn : n < C.birth p) :
    p ∉ (C.assignments n).primes := Nat.find_min (C.exhaustive p) hn

/-- The exact appearance-stage description supplies finiteness automatically. -/
theorem birth_le_iff_mem (p : PrimeIndex) (n : ℕ) :
    C.birth p ≤ n ↔ p ∈ (C.assignments n).primes := by
  constructor
  · intro h
    exact C.monotone_primes h (C.birth_mem p)
  · intro h
    exact Nat.find_min' (C.exhaustive p) h

theorem finite_initial_birth (n : ℕ) : {p : PrimeIndex | C.birth p ≤ n}.Finite := by
  apply (C.assignments n).primes.finite_toSet.subset
  intro p hp
  exact (C.birth_le_iff_mem p n).mp hp

/-- Guards are equal in every later finite approximation, not merely close. -/
theorem persistent_le {m n : ℕ} (hmn : m ≤ n) :
    ∀ p (hpm : p ∈ (C.assignments m).primes) (hpn : p ∈ (C.assignments n).primes),
      (C.assignments n).guard p hpn = (C.assignments m).guard p hpm := by
  induction n, hmn using Nat.le_induction with
  | base => intros; rfl
  | succ n hmn ih =>
    intro p hpm hpn
    have hp := C.monotone_primes hmn hpm
    exact (C.persistent n p hp hpn).trans (ih p hpm hp)

/-- The first stored guard supplies the unique eventual argument at this prime. -/
noncomputable def guard (p : PrimeIndex) : Guard p :=
  (C.assignments (C.birth p)).guard p (C.birth_mem p)

theorem guard_agrees (n : ℕ) (p : PrimeIndex) (hp : p ∈ (C.assignments n).primes) :
    (C.assignments n).guard p hp = C.guard p :=
  C.persistent_le ((C.birth_le_iff_mem p n).mpr hp) p (C.birth_mem p) hp

private theorem stored_birth_of_first (n : ℕ) (p : PrimeIndex)
    (hp : p ∈ (C.assignments n).primes)
    (hfirst : ∀ m < n, p ∉ (C.assignments m).primes) :
    ((C.assignments n).guard p hp).birth = n := by
  cases n with
  | zero => exact C.initial_birth p hp
  | succ n => exact C.new_birth n p hp (hfirst n (Nat.lt_succ_self n))

theorem guard_birth (p : PrimeIndex) : (C.guard p).birth = C.birth p :=
  C.stored_birth_of_first (C.birth p) p (C.birth_mem p)
    (fun _ hn => C.not_mem_before_birth p hn)

/-- Actual global p-adic guard arguments, inherited from the common stages. -/
noncomputable def value (p : PrimeIndex) : ℤ_[p.val] := (C.guard p).value

/-- Every later finite approximant uses exactly this same p-adic value. -/
theorem value_agrees (n : ℕ) (p : PrimeIndex) (hp : p ∈ (C.assignments n).primes) :
    ((C.assignments n).guard p hp).value = C.value p :=
  congrArg Guard.value (C.guard_agrees n p hp)

/-- Permanence identifies a unique global value, with no limiting approximation. -/
theorem existsUnique_value (p : PrimeIndex) :
    ∃! β : ℤ_[p.val], ∀ n (hp : p ∈ (C.assignments n).primes),
      ((C.assignments n).guard p hp).value = β := by
  refine ⟨C.value p, fun n hp => C.value_agrees n p hp, ?_⟩
  intro β hβ
  exact (hβ (C.birth p) (C.birth_mem p)).symm

theorem value_transcendental (p : PrimeIndex) : Transcendental ℚ (C.value p).val :=
  (C.guard p).transcendental

theorem value_unit (p : PrimeIndex) : IsUnit (C.value p) := (C.guard p).unit

/-- The stored representative of the unique global guard. -/
noncomputable def representative (p : PrimeIndex) : ℕ := (C.guard p).representative

theorem value_residue (p : PrimeIndex) :
    PadicInt.toZMod (C.value p) = (C.representative p : ZMod p.val) :=
  (C.guard p).residue

/-- Exactly the finite stage-zero batch may lack the logarithmic interval. -/
theorem eventually_logarithmic : ∀ᶠ p : PrimeIndex in Filter.cofinite,
    Nat.log 2 p.val ≤ C.representative p ∧ C.representative p ≤ 2 * Nat.log 2 p.val := by
  have hpos : ∀ᶠ p : PrimeIndex in Filter.cofinite, 0 < C.birth p := by
    apply Filter.eventually_cofinite.mpr
    simpa only [not_lt] using C.finite_initial_birth 0
  filter_upwards [hpos] with p hp
  exact (C.guard p).logarithmic (by rwa [C.guard_birth])

/-- The global family satisfies the paper's actual finite guard support. -/
theorem ratFunc_guardSupport_finite (f : RatFunc ℚ) (hf : f ≠ 0) :
    {p : PrimeIndex | EvaluationDVR.valuation p.val
      (guardEvaluation C.value C.value_transcendental p) f ≠ 1}.Finite :=
  LogarithmicGuards.ratFunc_guardSupport_finite C.value C.representative C.value_residue
    C.eventually_logarithmic C.value_transcendental f hf

/-- The same common-stage guard family paired with the primary arguments fixed
at the start of the construction. -/
noncomputable def places : PairedDomain.Places where
  primes := PrimaryChoices.primes.toEquiv
  primary := PrimaryChoices.primary
  primary_trans := PrimaryChoices.primary_transcendental
  primary_late := PrimaryChoices.primary_late
  guard := C.value
  guard_trans := C.value_transcendental

/-- For any nonzero-constant raw family, the resulting actual intersection has
the required integer localization, using the manuscript guard argument. -/
theorem integerLocalization {S : Set ℚ[X]} (hS : ∀ q ∈ S, constantCoeff q ≠ 0) :
    IsLocalization (IntersectionDomain.integerDenominators (PairedDomain.domain S C.places))
      (PoleAlgebra.generated S) := by
  apply PairedDomain.integerLocalization_of_guard_support C.places hS
  exact C.ratFunc_guardSupport_finite

end ApproximationChain

end UnconditionalCounterexample.PaperGuardStages
