import UnconditionalCounterexample.Variations.DyadicLedger
import UnconditionalCounterexample.Variations.DyadicSplitValues

/-!
# Implementing a split prescription with the ledger's unit choices

At every prime dividing the task modulus the reserved balanced column has
order zero. Its local multiplier is therefore free. The two branches use the
same whole-fibre assignment, while their actual target units may differ.
-/

noncomputable section

namespace UnconditionalCounterexample.Variations.DyadicLedger

open GuardSupport PrimaryChoices CombinedGuardStep Univariate MixedStageSelection

set_option backward.isDefEq.respectTransparency false

/-- The actual p-adic integer unit selected at a modulus prime for the reserved
raw. The matching condition is evaluated on the same branch at which the
completed polynomial will be tested. -/
def splitUnit {p : PrimeIndex} (site : Site p) (b first : Bool) (x u₀ : RatFunc ℚ)
    (h₀ : u₀ ≠ 0)
    (hmatch : ‖DyadicSplit.branchValue site b u₀‖ =
      if first then ‖DyadicSplit.branchValue site b x‖ else 1) : ℤ_[p.val]ˣ :=
  (DyadicSplit.reservedTarget_unit first (DyadicSplit.branchValue_ne_zero _ _ h₀) hmatch).choose

theorem splitUnit_value {p : PrimeIndex} (site : Site p) (b first : Bool) (x u₀ : RatFunc ℚ)
    (h₀ : u₀ ≠ 0)
    (hmatch : ‖DyadicSplit.branchValue site b u₀‖ =
      if first then ‖DyadicSplit.branchValue site b x‖ else 1) :
    ((splitUnit site b first x u₀ h₀ hmatch : ℤ_[p.val]) : ℚ_[p.val]) =
      DyadicSplit.reservedTarget first (DyadicSplit.branchValue site b x)
        (DyadicSplit.branchValue site b u₀) :=
  (DyadicSplit.reservedTarget_unit first (DyadicSplit.branchValue_ne_zero _ _ h₀) hmatch).choose_spec

/-- Use the eligible split's target units over the modulus and the given base
units elsewhere. This has precisely the fibrewise signature of `Driver.unit`.
-/
def splitUnits (B : Batch) (sites : Table B.assigned.primes) (m : ℕ) (first : ℕ → Bool)
    (x u₀ : RatFunc ℚ) (h₀ : u₀ ≠ 0) (base : (j : B.indices) → Bool → ℤ_[B.primeAt j]ˣ)
    (hmatch : ∀ j : B.indices, B.primeAt j ∣ m → ∀ b,
      ‖DyadicSplit.branchValue (siteAt B sites j) b u₀‖ =
        if first (B.primeAt j) then ‖DyadicSplit.branchValue (siteAt B sites j) b x‖ else 1)
    (j : B.indices) (b : Bool) : ℤ_[B.primeAt j]ˣ :=
  if h : B.primeAt j ∣ m then
    splitUnit (siteAt B sites j) b (first (B.primeAt j)) x u₀ h₀ (hmatch j h b)
  else base j b

def splitPrecision (B : Batch) (m : ℕ) (base : B.indices → Bool → ℕ)
    (j : B.indices) (b : Bool) : ℕ :=
  if B.primeAt j ∣ m then m.factorization (B.primeAt j) else base j b

theorem splitUnits_value (B : Batch) (sites : Table B.assigned.primes) (m : ℕ) (first : ℕ → Bool)
    (x u₀ : RatFunc ℚ) (h₀ : u₀ ≠ 0) (base : (j : B.indices) → Bool → ℤ_[B.primeAt j]ˣ)
    (hmatch : ∀ j : B.indices, B.primeAt j ∣ m → ∀ b,
      ‖DyadicSplit.branchValue (siteAt B sites j) b u₀‖ =
        if first (B.primeAt j) then ‖DyadicSplit.branchValue (siteAt B sites j) b x‖ else 1)
    (j : B.indices) (b : Bool) (hj : B.primeAt j ∣ m) :
    ((splitUnits B sites m first x u₀ h₀ base hmatch j b : ℤ_[B.primeAt j]) : ℚ_[B.primeAt j]) =
      DyadicSplit.reservedTarget (first (B.primeAt j)) (DyadicSplit.branchValue (siteAt B sites j) b x)
        (DyadicSplit.branchValue (siteAt B sites j) b u₀) := by
  rw [splitUnits, dite_eq_left hj, splitUnit_value]

/-- A reserved balanced generator is a unit over every prime whose permanent
role lies outside its two regular sites. This also covers lone guards and
auxiliary primaries. -/
theorem balanced_atPrimary_zero (k : Bool) (n : ℕ) (p : PrimeIndex) (role : Option FibreRole)
    (hfresh : ∀ c, role ≠ some (.regular c k n)) :
    (RawColumn.balanced k n).atPrimary p role = 0 := by
  cases role with
  | none => rfl
  | some r =>
    cases r with
    | auxiliary => rfl
    | regular c l i =>
      have h : ¬ (k = l ∧ n = i) := by rintro ⟨rfl, rfl⟩; exact hfresh c rfl
      simp [RawColumn.atPrimary, h]

private theorem targets_ext {B : Batch} {sites : Table B.assigned.primes} {a b : Targets B sites}
    (hv : a.value = b.value) (hk : a.precision = b.precision) : a = b := by
  cases a
  cases b
  simp_all

namespace Driver

variable (D : Driver)

/-- Every prime dividing a reserved task's modulus belongs to the actual stage
batch, whether processed earlier or introduced by this request. -/
theorem reserved_primes_processed (n : ℕ) (t : SplitTask) (hr : (D.actualRequest n).reserve = true)
    (ht : ((D.state n).pending ++ (D.actualRequest n).enqueue).head? = some t)
    (p : PrimeIndex) (hp : p.val ∣ t.modulus) :
    p ∈ (selection D.requirements n).batch.processed.primes := by
  have he := (D.actualRequest n).reserve_primes hr t ht p hp
  rcases Finset.mem_union.mp he with hold | hnew
  · rw [(selection D.requirements n).progress.processed]
    exact PaperGuardStages.subset_nextPrimes _ _ _ hold
  · exact D.schedule.requested_processed n hnew

/-- Choosing the callback units at a reserved stage makes the ledger target
table itself the overlay accepted by the global conductor descent. Outside
the modulus its previous values and precisions may be arbitrary. -/
theorem actualTargets_eq_reserved (n m : ℕ) (first : ℕ → Bool) (x u₀ : RatFunc ℚ)
    (hx : x ≠ 0) (h₀ : u₀ ≠ 0)
    (hzero : ∀ j : (selection D.requirements n).batch.indices, (primes j.val).val ∣ m →
      (D.actualRequest n).column.atPrimary (primes j.val) ((D.actualRequest n).nextRole (primes j.val)) = 0)
    (hunit : ∀ j : (selection D.requirements n).batch.indices, (primes j.val).val ∣ m → ∀ b,
      (D.unit (D.state n) ((chain D.requirements).approx n) (table D.requirements n)
        (selection D.requirements n).batch (table D.requirements (n+1)) j b).val.val =
        DyadicSplit.reservedTarget (first (primes j.val).val)
          (DyadicSplit.branchValue (selectionSite D.requirements n j) b x)
          (DyadicSplit.branchValue (selectionSite D.requirements n j) b u₀))
    (hprecision : ∀ j : (selection D.requirements n).batch.indices, (primes j.val).val ∣ m → ∀ b,
      D.precision (D.state n) ((chain D.requirements).approx n) (table D.requirements n)
        (selection D.requirements n).batch (table D.requirements (n+1)) j b = m.factorization (primes j.val).val) :
    actualTargets D.requirements n =
      DyadicSplit.reserveTargets _ _ (actualTargets D.requirements n) m first x u₀ hx h₀ := by
  apply targets_ext
  · funext j b
    by_cases hj : (selection D.requirements n).batch.primeAt j ∣ m
    · simp only [DyadicSplit.reserveTargets, ite_eq_left hj]
      rw [D.actualTarget_value, hzero j hj, ite_self, zpow_zero, one_mul, hunit j hj]
      rfl
    · simp only [DyadicSplit.reserveTargets, ite_eq_right hj]
  · funext j b
    by_cases hj : (selection D.requirements n).batch.primeAt j ∣ m
    · simp only [DyadicSplit.reserveTargets, ite_eq_left hj, D.actualTarget_precision]
      exact hprecision j hj b
    · simp only [DyadicSplit.reserveTargets, ite_eq_right hj]

/-- The actual program-selected normalized raw uses the desired units at a
reserved task. Only its ordinary free-unit and precision callbacks and the
zero column order at the modulus are specified. -/
theorem selected_split_congruences (n : ℕ) (m : ℕ) (first : ℕ → Bool) (x u₀ : RatFunc ℚ)
    (hx : x ≠ 0) (h₀ : u₀ ≠ 0) (i : (selection D.requirements n).batch.indices)
    (b : Bool) (hb : Active (permanentSite D.requirements (primes i.val)).paired b)
    (hint : (permanentSite D.requirements (primes i.val)).evaluate b hb x ∈ PadicInt.subring (primes i.val).val)
    (hmatch : ‖(permanentSite D.requirements (primes i.val)).evaluate b hb u₀‖ =
      if first (primes i.val).val then ‖(permanentSite D.requirements (primes i.val)).evaluate b hb x‖ else 1)
    (hz : (D.actualRequest n).column.atPrimary (primes i.val) ((D.actualRequest n).nextRole (primes i.val)) = 0)
    (hunit : (D.unit (D.state n) ((chain D.requirements).approx n) (table D.requirements n)
        (selection D.requirements n).batch (table D.requirements (n+1)) i b).val.val = DyadicSplit.reservedTarget (first (primes i.val).val)
          ((permanentSite D.requirements (primes i.val)).evaluate b hb x)
          ((permanentSite D.requirements (primes i.val)).evaluate b hb u₀))
    (hprecision : D.precision (D.state n) ((chain D.requirements).approx n) (table D.requirements n)
        (selection D.requirements n).batch (table D.requirements (n+1)) i b =
          m.factorization (primes i.val).val) :
    let p := (primes i.val).val
    let f := (permanentSite D.requirements (primes i.val)).evaluate b hb
    let u := u₀*(chain D.requirements).generators n
    let v := x/u
    (f u - (if first p then f x else 1)) / (p : ℚ_[p]) ^ m.factorization p ∈ PadicInt.subring p ∧
      (f v - (if first p then 1 else f x)) / (p : ℚ_[p]) ^ m.factorization p ∈ PadicInt.subring p := by
  obtain ⟨hg, he⟩ := processed_value D.requirements n i b hb
  dsimp only at hg he ⊢
  rw [D.actualTarget_value, hz, ite_self, zpow_zero, one_mul, hunit] at hg he
  rw [D.actualTarget_precision, hprecision] at he
  simpa only [map_mul, map_div₀] using DyadicSplit.factor_congruences (first (primes i.val).val)
    _ _ _ _ ((map_ne_zero _).mpr hx) ((map_ne_zero _).mpr h₀) hint hmatch hg he

end Driver
end UnconditionalCounterexample.Variations.DyadicLedger
