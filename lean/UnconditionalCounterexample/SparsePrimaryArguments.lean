import UnconditionalCounterexample.SparsePrimaryDomain

/-!
# Actual active arguments for mixed one-point and paired stages

A static injective prime sequence and its primary arguments are transported
to the p-adic integer type at any selected prime, with exact agreement at the
original sequence indices. These constructions do not depend on a final
guard family. The current batch guard may be supplied separately.

`BranchActive` retains the true (guard) branch at every prime and the false
(primary) branch only at selected primes. `branchAt` is a total array with
zero in the inactive entry; all transcendence/distinctness claims concern
active branches. Positive primary valuation and the actual guard's unit
property prove separation. This is the concrete input geometry for the
mixed §8.2 finite selector, not an assumed polynomial-selection conclusion.
-/

noncomputable section
namespace UnconditionalCounterexample.SparsePrimaryDomain
open GuardSupport

/-- The unique sequence index of a prime in an embedding's range. -/
def primaryIndexOf (primes : ℕ ↪ PrimeIndex) (p : PrimeIndex)
    (hp : p ∈ Set.range primes) : ℕ :=
  (Equiv.ofInjective primes primes.injective).symm ⟨p, hp⟩

@[simp] theorem prime_primaryIndexOf (primes : ℕ ↪ PrimeIndex) (p : PrimeIndex)
    (hp : p ∈ Set.range primes) : primes (primaryIndexOf primes p hp) = p :=
  Equiv.apply_ofInjective_symm primes.injective ⟨p, hp⟩

@[simp] theorem primaryIndexOf_prime (primes : ℕ ↪ PrimeIndex) (j : ℕ)
    (hp : primes j ∈ Set.range primes) : primaryIndexOf primes (primes j) hp = j :=
  primes.injective (prime_primaryIndexOf primes (primes j) hp)

private theorem cast_dependent_apply {I J : Type*} (F : J → Type*)
    (f : I → J) (g : ∀ i, F (f i)) {i j : I} (hij : i = j) (h : f i = f j) :
    cast (congrArg F h) (g i) = g j := by
  subst j
  rfl

private theorem predicate_cast {J : Type*} (F : J → Type*) (P : ∀ j, F j → Prop)
    {i j : J} (h : i = j) (x : F i) (hx : P i x) :
    P j (cast (congrArg F h) x) := by
  subst j
  exact hx

/-- The actual selected primary, transported to the p-adic integer type at p. -/
def primaryAtOf (primes : ℕ ↪ PrimeIndex) (primary : ∀ j, ℤ_[(primes j).val])
    (p : PrimeIndex) (hp : p ∈ Set.range primes) : ℤ_[p.val] :=
  cast (congrArg (fun q : PrimeIndex => ℤ_[q.val]) (prime_primaryIndexOf primes p hp))
    (primary (primaryIndexOf primes p hp))

@[simp] theorem primaryAtOf_prime (primes : ℕ ↪ PrimeIndex)
    (primary : ∀ j, ℤ_[(primes j).val]) (j : ℕ)
    (hp : primes j ∈ Set.range primes) : primaryAtOf primes primary (primes j) hp = primary j := by
  unfold primaryAtOf
  exact cast_dependent_apply (fun q : PrimeIndex => ℤ_[q.val]) primes primary
    (primaryIndexOf_prime primes j hp) (prime_primaryIndexOf primes (primes j) hp)

theorem primaryAtOf_transcendental (primes : ℕ ↪ PrimeIndex)
    (primary : ∀ j, ℤ_[(primes j).val])
    (ht : ∀ j, Transcendental ℚ (primary j).val)
    (p : PrimeIndex) (hp : p ∈ Set.range primes) :
    Transcendental ℚ (primaryAtOf primes primary p hp).val := by
  unfold primaryAtOf
  exact predicate_cast (fun q : PrimeIndex => ℤ_[q.val])
    (fun q z => Transcendental ℚ z.val) (prime_primaryIndexOf primes p hp)
    (primary (primaryIndexOf primes p hp)) (ht (primaryIndexOf primes p hp))

end UnconditionalCounterexample.SparsePrimaryDomain

namespace UnconditionalCounterexample.SparsePrimaryDomain
open GuardSupport

/-- The guard is always active, and the primary only at retained primes. -/
def BranchActive (primes : ℕ ↪ PrimeIndex) (p : PrimeIndex) (b : Bool) : Prop :=
  b = true ∨ p ∈ Set.range primes

/-- A mixed branch array using only a static primary family and the current
guard at p. Requirements are imposed only on active entries. -/
noncomputable def branchAt (primes : ℕ ↪ PrimeIndex)
    (primary : ∀ j, ℤ_[(primes j).val]) (p : PrimeIndex) (guard : ℤ_[p.val])
    (b : Bool) : ℚ_[p.val] := by
  classical
  exact if b then guard.val else if hp : p ∈ Set.range primes then
    (primaryAtOf primes primary p hp).val else 0

@[simp] theorem branchAt_true (primes : ℕ ↪ PrimeIndex)
    (primary : ∀ j, ℤ_[(primes j).val]) (p : PrimeIndex) (guard : ℤ_[p.val]) :
    branchAt primes primary p guard true = guard.val := by
  simp only [branchAt, ↓reduceIte]

@[simp] theorem branchAt_false_selected (primes : ℕ ↪ PrimeIndex)
    (primary : ∀ j, ℤ_[(primes j).val]) (p : PrimeIndex) (guard : ℤ_[p.val])
    (hp : p ∈ Set.range primes) :
    branchAt primes primary p guard false = (primaryAtOf primes primary p hp).val := by
  simp only [branchAt, Bool.false_eq_true, ↓reduceIte, hp, ↓reduceDIte]

@[simp] theorem branchAt_false_prime (primes : ℕ ↪ PrimeIndex)
    (primary : ∀ j, ℤ_[(primes j).val]) (j : ℕ) (guard : ℤ_[(primes j).val]) :
    branchAt primes primary (primes j) guard false = (primary j).val := by
  rw [branchAt_false_selected primes primary _ guard ⟨j, rfl⟩]
  exact congrArg Subtype.val (primaryAtOf_prime primes primary j _)

theorem branchAt_transcendental (primes : ℕ ↪ PrimeIndex)
    (primary : ∀ j, ℤ_[(primes j).val])
    (hprimary : ∀ j, Transcendental ℚ (primary j).val)
    (p : PrimeIndex) (guard : ℤ_[p.val]) (hguard : Transcendental ℚ guard.val)
    (b : Bool) (hb : BranchActive primes p b) :
    Transcendental ℚ (branchAt primes primary p guard b) := by
  cases b with
  | true => simpa only [branchAt_true] using hguard
  | false =>
    have hp : p ∈ Set.range primes := hb.resolve_left (by decide)
    rw [branchAt_false_selected primes primary p guard hp]
    exact primaryAtOf_transcendental primes primary hprimary p hp

theorem padicInt_not_unit_of_pos_valuation (p : PrimeIndex) (a : ℤ_[p.val])
    (ha : 0 < a.val.valuation) : ¬ IsUnit a := by
  have hne : a.val ≠ 0 := by intro h; simp [h] at ha
  apply PadicInt.not_isUnit_iff.mpr
  change ‖a.val‖ < 1
  rw [Padic.norm_eq_zpow_neg_valuation hne]
  exact (zpow_lt_one_iff_right₀ (by exact_mod_cast p.property.one_lt)).mpr (by omega)

theorem branchAt_ne_of_selected (primes : ℕ ↪ PrimeIndex)
    (primary : ∀ j, ℤ_[(primes j).val])
    (hprimary : ∀ j, ¬ IsUnit (primary j)) (p : PrimeIndex)
    (hp : p ∈ Set.range primes) (guard : ℤ_[p.val]) (hguard : IsUnit guard) :
    branchAt primes primary p guard false ≠ branchAt primes primary p guard true := by
  obtain ⟨j, rfl⟩ := hp
  rw [branchAt_false_prime, branchAt_true]
  intro heq
  have heq' : primary j = guard := Subtype.ext heq
  exact hprimary j (heq'.symm ▸ hguard)

/-- Every primary in the sparse place data is a nonunit once the exceptional
first value is fixed to two; the later values are already one. -/
theorem primary_not_unit (d : Places) (hfirst : (d.primary 0).val.valuation = 2) (j : ℕ) :
    ¬ IsUnit (d.primary j) := by
  apply padicInt_not_unit_of_pos_valuation
  by_cases hj : j = 0
  · subst j
    rw [hfirst]
    decide
  · rw [d.primary_late j (Nat.pos_of_ne_zero hj)]
    decide

/-- Nonunit status transports to the selected primary above p. -/
theorem primaryAtOf_not_unit (primes : ℕ ↪ PrimeIndex)
    (primary : ∀ j, ℤ_[(primes j).val]) (hprimary : ∀ j, ¬ IsUnit (primary j))
    (p : PrimeIndex) (hp : p ∈ Set.range primes) :
    ¬ IsUnit (primaryAtOf primes primary p hp) := by
  obtain ⟨j, rfl⟩ := hp
  exact (primaryAtOf_prime primes primary j _).symm ▸ hprimary j

/-- The static selected-primary choices have strictly positive valuation at
every index, including the exceptional first choice. -/
theorem selectedPrimary_not_unit (primes : ℕ → PrimeIndex) (j : ℕ) :
    ¬ IsUnit (SelectedPrimes.primary primes j) := by
  apply padicInt_not_unit_of_pos_valuation
  rw [SelectedPrimes.primary_valuation]
  unfold PrimaryChoices.order
  split <;> decide

end UnconditionalCounterexample.SparsePrimaryDomain
