import UnconditionalCounterexample.Variations.UnivariatePrimary

/-!
# A two-centre client on the actual infinite polynomial sequence

One odd primary is born at each stage. Its centre, displacement and
normalized value prescriptions may differ by stage. Every other prime has
only a guard, and the dyadic guard is 3 modulo 4. All statements here refer
to the very same infinite sequence that supplies the moving polynomials.
-/

noncomputable section

namespace UnconditionalCounterexample.Variations.UnivariateClient

open Polynomial GuardSupport PrimaryChoices CombinedGuardStep RecursivePrefix Univariate

abbrev TargetRule := ∀ {n} (P : Prefix n), Table P.state.assignment.primes →
  (B : Batch) → (sites : Table B.assigned.primes) → Targets B sites

structure Family where
  colour : ℕ → Bool
  order : ℕ → ℕ
  positive : ∀ n, 0 < order n
  targets : TargetRule

namespace Family
variable (F : Family)

def schedule : Schedule where
  births := fun {n} P _ => (UnivariatePrimary.choose P (F.colour n) (F.order n) (F.positive n)).births
  base := UnivariateGuards.base
  targets := F.targets

abbrev requirements := F.schedule.requirements
abbrev atStage (n : ℕ) :=
  UnivariatePrimary.choose ((chain F.requirements).approx n) (F.colour n) (F.order n) (F.positive n)
abbrev prime (n : ℕ) : PrimeIndex := (F.atStage n).prime

theorem mem_chosen (n : ℕ) : F.prime n ∈ (F.schedule.chosen n).primes :=
  Finset.mem_singleton_self _

theorem prime_injective : Function.Injective F.prime := by
  intro m n h
  exact F.schedule.requested_unique (F.mem_chosen m) (h ▸ F.mem_chosen n)

theorem permanent_eq (n : ℕ) :
    permanentSite F.requirements (F.prime n) =
      ⟨(F.atStage n).guard.value, (F.atStage n).guard.transcendental, some (F.atStage n).primary⟩ :=
  (F.schedule.permanentSite_requested n _ (F.mem_chosen n)).trans
    ((F.atStage n).site_eq (F.mem_chosen n))

theorem paired_iff (p : PrimeIndex) : (permanentSite F.requirements p).paired ↔ ∃ n, p = F.prime n := by
  rw [F.schedule.permanent_paired_iff]
  constructor
  · rintro ⟨n, h, _⟩
    exact ⟨n, Finset.mem_singleton.mp h⟩
  · rintro ⟨n, rfl⟩
    exact ⟨n, F.mem_chosen n, rfl⟩

/-- The actual global guard satisfies the same residue requirements as its
first assignment. This also covers every non-primary prime. -/
theorem guard_residues (p : PrimeIndex) :
    (p.val = 2 → PadicInt.toZModPow 2 (permanentSite F.requirements p).guard = 3) ∧
    (p.val ≠ 2 → PadicInt.toZMod (permanentSite F.requirements p).guard ≠ 1) := by
  let R := F.requirements
  let C := (chain R).guardChain
  let n := C.birth p
  let P := (chain R).approx n
  let sel := selection R n
  have hp : p ∈ sel.batch.assigned.primes := C.birth_mem p
  have hf : p ∉ P.state.assignment.primes := by
    change p ∉ ((chain R).approx n).state.assignment.primes
    cases hn : n with
    | zero => exact Finset.notMem_empty p
    | succ m =>
      intro hm
      exact C.not_mem_before_birth p (n := m) (by change m < n; omega) hm
  by_cases h : p ∈ (F.schedule.chosen n).primes
  · have he : p = F.prime n := Finset.mem_singleton.mp h
    rw [he, F.permanent_eq n]
    exact ⟨(F.atStage n).guard_good.dyadic, (F.atStage n).guard_good.odd⟩
  · have start : n = 0 → P.state = zeroState := by
      intro hn
      change ((chain R).approx n).state = _
      rw [hn]
      rfl
    let b := UnivariateGuards.base P start sel.plan.degree (F.schedule.chosen n).primes
    have he : sel.batch = (F.schedule.chosen n).batch b.val := sel.batch_used start
    have hb : p ∈ b.val.assigned.primes := by rw [he] at hp; exact hp
    have hg := UnivariateGuards.base_good P start sel.plan.degree (F.schedule.chosen n).primes p hb hf
    rw [(F.schedule.permanentSite_other n p hf h hp).2 start hb]
    exact ⟨hg.dyadic, hg.odd⟩

theorem dyadic_guard_only :
    let p : PrimeIndex := ⟨2, Nat.prime_two⟩
    (permanentSite F.requirements p).primary = none ∧
    PadicInt.toZModPow 2 (permanentSite F.requirements p).guard = 3 := by
  let p : PrimeIndex := ⟨2, Nat.prime_two⟩
  have hn : ¬ (permanentSite F.requirements p).paired := by
    rw [F.paired_iff]
    rintro ⟨n, h⟩
    have := (F.atStage n).odd
    exact this.ne (congrArg Subtype.val h)
  refine ⟨?_, (F.guard_residues p).1 rfl⟩
  cases he : (permanentSite F.requirements p).primary with
  | none => rfl
  | some a => exact (hn (by simp [Site.paired, he])).elim

/-- Earlier selected polynomials are units at both actual branches of a
newly allocated primary, regardless of its colour. -/
theorem old_units (n j : ℕ) (hj : j < n) :
    ‖((chain F.requirements).raw j).eval₂ (algebraMap ℚ ℚ_[(F.prime n).val])
      ((permanentSite F.requirements (F.prime n)).branch false)‖ = 1 ∧
    ‖((chain F.requirements).raw j).eval₂ (algebraMap ℚ ℚ_[(F.prime n).val])
      ((permanentSite F.requirements (F.prime n)).branch true)‖ = 1 := by
  rw [F.permanent_eq, ← (chain F.requirements).raw_agrees n ⟨j,hj⟩]
  exact ⟨(F.atStage n).old_primary_units ⟨j,hj⟩, (F.atStage n).old_guard_units ⟨j,hj⟩⟩

end Family

/-- The client alternates centres and prescribes a nonunit primary target
at every stage, with all active guard targets equal to one. -/
def alternating : Family where
  colour := fun n => decide (n % 2 = 1)
  order := fun n => if n < 2 then 2 else 1
  positive := fun n => by split <;> decide
  targets := fun {n} _ _ B _ => {
    value := fun j b => if b then 1 else (B.primeAt j : ℚ_[B.primeAt j]) ^ 3
    precision := fun _ _ => n + 1
    nonzero := fun j b _ => by
      have hp : (B.primeAt j : ℚ_[B.primeAt j]) ≠ 0 :=
        Nat.cast_ne_zero.mpr (Fact.out : (B.primeAt j).Prime).ne_zero
      cases b <;> simp [hp] }

/-- One concrete sequence has a single dyadic guard and distinct odd fibres
whose first primaries have displacement order two from 0 and 1. -/
theorem opposite_centres :
    let R := alternating.requirements
    let p₀ := alternating.prime 0
    let p₁ := alternating.prime 1
    let two : PrimeIndex := ⟨2, Nat.prime_two⟩
    p₀ ≠ p₁ ∧ (permanentSite R two).primary = none ∧
    PadicInt.toZModPow 2 (permanentSite R two).guard = 3 ∧
    (permanentSite R p₀).paired ∧ (permanentSite R p₁).paired ∧
    ((permanentSite R p₀).branch false).valuation = 2 ∧
    ((permanentSite R p₁).branch false - 1).valuation = 2 := by
  dsimp only
  refine ⟨alternating.prime_injective.ne (by decide), alternating.dyadic_guard_only.1,
    alternating.dyadic_guard_only.2, ?_, ?_, ?_, ?_⟩
  · rw [alternating.permanent_eq]; rfl
  · rw [alternating.permanent_eq]; rfl
  · rw [alternating.permanent_eq]
    have h := (alternating.atStage 0).hv
    change ((alternating.atStage 0).primary.val.val - 0).valuation = 2 at h
    rw [sub_zero] at h
    exact h
  · rw [alternating.permanent_eq]
    exact (alternating.atStage 1).hv

end UnconditionalCounterexample.Variations.UnivariateClient
