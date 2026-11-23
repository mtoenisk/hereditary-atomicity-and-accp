import UnconditionalCounterexample.Variations.DyadicFreshFibres
import UnconditionalCounterexample.Variations.UnivariateGuards

/-!
# Processing the modulus of a reserved split

Every prime dividing the modulus is present when the free balanced column is
chosen. If the prime has just been requested as a primary, that primary and
its role are kept. Other missing primes receive ordinary two-centre guards.
-/

noncomputable section
namespace UnconditionalCounterexample.Variations.DyadicLedger.FreshFibres

open GuardSupport RecursivePrefix Univariate PaperGuardStages CombinedGuardStep

variable {n : ℕ} {m : Ledger} {P : Prefix n}

private theorem exists_guard (P : Prefix n) (p : PrimeIndex) (fresh : p ∉ P.state.assignment.primes) :
    ∃ g : Guard p, g.birth = n ∧ UnivariateGuards.Good g ∧
      ∀ j : Fin n, ‖(P.raw j).eval₂ (algebraMap ℚ ℚ_[p.val]) g.value.val‖ = 1 := by
  by_cases h : n = 0
  · subst n
    obtain ⟨g,hb,hg⟩ := UnivariateGuards.exists_initial_guard p
    exact ⟨g,hb,hg,fun j => Fin.elim0 j⟩
  · let start : n = 0 → P.state = zeroState := fun h' => (h h').elim
    let B := UnivariateGuards.base P start 1 {p}
    have hp : p ∈ B.val.assigned.primes := by
      apply B.val.processed_subset_assigned
      rw [B.property.processed]
      simp
    have born := B.property.new_guard p hp fresh
    exact ⟨B.val.assigned.guard p hp,born.1,UnivariateGuards.base_good P start 1 {p} p hp fresh,born.2⟩

private def missing (a : FreshFibres m P) (needed : Finset PrimeIndex) : Finset PrimeIndex :=
  needed \ (P.state.assignment.primes ∪ a.births.primes)

private theorem missing_fresh (a : FreshFibres m P) (needed : Finset PrimeIndex)
    (p : PrimeIndex) (hp : p ∈ missing a needed) : p ∉ P.state.assignment.primes :=
  fun h => (Finset.mem_sdiff.mp hp).2 (Finset.mem_union_left _ h)

private def padding (a : FreshFibres m P) (needed : Finset PrimeIndex) : FreshFibres m P where
  births := {
    primes := missing a needed
    fresh := missing_fresh a needed
    guard := fun p hp => (exists_guard P p (missing_fresh a needed p hp)).choose
    birth_eq := fun p hp => (exists_guard P p (missing_fresh a needed p hp)).choose_spec.1
    old_units := fun p hp => (exists_guard P p (missing_fresh a needed p hp)).choose_spec.2.2
    primary := fun _ _ => none }
  role := fun _ _ => none
  paired := fun _ _ => Iff.rfl
  primary_before := fun _ _ h => False.elim (by contradiction)
  new_regular := by simp
  distinct_regular := by simp

private theorem disjoint_padding (a : FreshFibres m P) (needed : Finset PrimeIndex) :
    Disjoint a.births.primes (padding a needed).births.primes := by
  apply Finset.disjoint_left.mpr
  intro p h h'
  exact (Finset.mem_sdiff.mp h').2 (Finset.mem_union_right _ h)

/-- Extend a new regular/auxiliary request to include any finite set of
primes at which the reserved raw will have to attain a unit target. -/
def coverPrimes (a : FreshFibres m P) (needed : Finset PrimeIndex) : FreshFibres m P :=
  a.unionAux (padding a needed) (disjoint_padding a needed) (by intros; simp [padding])

theorem coverPrimes_covered (a : FreshFibres m P) (needed : Finset PrimeIndex) :
    needed ⊆ P.state.assignment.primes ∪ (a.coverPrimes needed).births.primes := by
  intro p hp
  by_cases old : p ∈ P.state.assignment.primes
  · exact Finset.mem_union_left _ old
  apply Finset.mem_union_right
  by_cases req : p ∈ a.births.primes
  · exact Finset.mem_union_left _ req
  · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hp, fun h => (Finset.mem_union.mp h).elim old req⟩)

theorem coverPrimes_old (a : FreshFibres m P) (needed : Finset PrimeIndex)
    (p : PrimeIndex) (hp : p ∈ a.births.primes) :
    ∃ h : p ∈ (a.coverPrimes needed).births.primes,
      (a.coverPrimes needed).role p h = a.role p hp ∧
      (a.coverPrimes needed).births.site p h = a.births.site p hp :=
  ⟨Finset.mem_union_left _ hp, a.unionAux_role_left _ _ _ p hp,
    a.births.union_site_left _ (disjoint_padding a needed) p hp⟩

theorem coverPrimes_extra (a : FreshFibres m P) (needed : Finset PrimeIndex) (p : PrimeIndex)
    (hp : p ∈ (a.coverPrimes needed).births.primes) (extra : p ∉ a.births.primes) :
    (a.coverPrimes needed).role p hp = none ∧
      UnivariateGuards.Good ((a.coverPrimes needed).births.guard p hp) := by
  let h := (Finset.mem_union.mp hp).resolve_left extra
  refine ⟨a.unionAux_role_right _ _ _ p h, ?_⟩
  have hs := a.births.union_site_right (padding a needed).births (disjoint_padding a needed) p h
  have hv := congrArg Site.guard hs
  change ((a.coverPrimes needed).births.guard p hp).value =
    (exists_guard P p (missing_fresh a needed p h)).choose.value at hv
  have hg := (exists_guard P p (missing_fresh a needed p h)).choose_spec.2.1
  constructor
  · intro h₂
    rw [hv]
    exact hg.dyadic h₂
  · intro h₂
    rw [hv]
    exact hg.odd h₂

/-- The positive modulus contributes finitely many rational primes. -/
def modulusPrimes (d : ℕ) : Finset PrimeIndex := d.primeFactors.subtype Nat.Prime

theorem modulus_covered (a : FreshFibres m P) {d : ℕ} (hd : 0 < d) (p : PrimeIndex) (hp : p.val ∣ d) :
    p ∈ P.state.assignment.primes ∪ (a.coverPrimes (modulusPrimes d)).births.primes :=
  a.coverPrimes_covered _ (Finset.mem_subtype.mpr (Nat.mem_primeFactors.mpr ⟨p.property,hp,hd.ne'⟩))

end UnconditionalCounterexample.Variations.DyadicLedger.FreshFibres
