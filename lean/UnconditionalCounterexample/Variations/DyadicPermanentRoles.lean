import UnconditionalCounterexample.Variations.DyadicFreshFibres
import UnconditionalCounterexample.Variations.DyadicLedgerValues

/-!
# Permanent prime labels of the actual dyadic selection

A label read at the same finite stage as the permanent site agrees with
every later table. Regular labels are injective globally, including when the
two labels were requested in different rounds.
-/

noncomputable section
namespace UnconditionalCounterexample.Variations.DyadicLedger.Driver
open GuardSupport RecursivePrefix Univariate

variable (D : Driver)

abbrev assigned (n : ℕ) := ((chain D.requirements).approx n).state.assignment.primes

theorem assigned_prime (p : PrimeIndex) : p ∈ D.assigned p.val :=
  ((chain D.requirements).approx p.val).state.covered ((GuardStages.mem_primesThrough _ _).mpr
    ((chain D.requirements).approx p.val).stage_cutoff)

/-- Role of the same fibre chosen by the univariate permanent-site table. -/
def permanentRole (p : PrimeIndex) := (D.state p.val).role p

theorem role_agrees {i j : ℕ} (hij : i ≤ j) (p : PrimeIndex) (h : p ∈ D.assigned i) :
    (D.state j).role p = (D.state i).role p := by
  induction j,hij using Nat.le_induction with
  | base => rfl
  | succ j hj ih => exact (D.role_old j p (assigned_mono D.requirements hj h)).trans ih

theorem role_eq_permanent {n : ℕ} (p : PrimeIndex) (h : p ∈ D.assigned n) :
    (D.state n).role p = D.permanentRole p := by
  rcases le_total n p.val with hle | hle
  · exact (D.role_agrees hle p h).symm
  · exact D.role_agrees hle p (D.assigned_prime p)

theorem permanentRole_requested {n : ℕ} (p : PrimeIndex) (hp : p ∈ (D.actualRequest n).births.primes) :
    D.permanentRole p = (D.actualRequest n).role p hp := by
  have h : p ∈ D.assigned (n+1) :=
    (selection D.requirements n).batch.processed_subset_assigned (D.schedule.requested_processed n hp)
  exact (D.role_eq_permanent p h).symm.trans (D.role_persistent p hp (Nat.lt_succ_self _))

private theorem stateRole_requested (n : ℕ) (p : PrimeIndex) (r : FibreRole)
    (h : (D.state n).role p = some r) :
    ∃ i < n, ∃ hi : p ∈ (D.actualRequest i).births.primes, (D.actualRequest i).role p hi = some r := by
  induction n with
  | zero => change none = some r at h; contradiction
  | succ n ih =>
    rw [state_succ] at h
    by_cases hp : p ∈ (D.actualRequest n).births.primes
    · exact ⟨n,Nat.lt_succ_self _,hp,by simpa [Request.update,Request.nextRole,hp] using h⟩
    · obtain ⟨i,hi,hm,hr⟩ := ih (by simpa [Request.update,Request.nextRole,hp] using h)
      exact ⟨i,by omega,hm,hr⟩

theorem permanentRole_iff (p : PrimeIndex) (r : FibreRole) :
    D.permanentRole p = some r ↔
      ∃ i, ∃ hi : p ∈ (D.actualRequest i).births.primes, (D.actualRequest i).role p hi = some r := by
  constructor
  · intro h
    obtain ⟨i,_,hi,hr⟩ := D.stateRole_requested p.val p r h
    exact ⟨i,hi,hr⟩
  · rintro ⟨i,hi,hr⟩
    exact (D.permanentRole_requested p hi).trans hr

theorem paired_iff_role (p : PrimeIndex) :
    (permanentSite D.requirements p).paired ↔ (D.permanentRole p).isSome := by
  rw [D.schedule.permanent_paired_iff]
  constructor
  · rintro ⟨n,hp,h⟩
    rw [D.permanentRole_requested p hp]
    exact ((D.actualRequest n).paired p hp).mp h
  · intro h
    obtain ⟨r,hr⟩ := Option.isSome_iff_exists.mp h
    obtain ⟨i,hi,hs⟩ := (D.permanentRole_iff p r).mp hr
    exact ⟨i,hi,((D.actualRequest i).paired p hi).mpr (by simp [hs])⟩

theorem permanent_regular_unique {p q : PrimeIndex} {c k : Bool} {i : ℕ}
    (hp : D.permanentRole p = some (.regular c k i)) (hq : D.permanentRole q = some (.regular c k i)) :
    p = q := by
  obtain ⟨t,ht,hr⟩ := (D.permanentRole_iff _ _).mp hp
  obtain ⟨u,hu,hs⟩ := (D.permanentRole_iff _ _).mp hq
  rcases lt_trichotomy t u with lt | eq | gt
  · exact False.elim ((D.actualRequest u).new_regular q hu c k i hs p
      ((D.role_persistent p ht lt).trans hr))
  · subst u
    exact (D.actualRequest t).distinct_regular p ht q hu c k i hr hs
  · exact False.elim ((D.actualRequest t).new_regular p ht c k i hr q
      ((D.role_persistent q hu gt).trans hs))

end UnconditionalCounterexample.Variations.DyadicLedger.Driver
