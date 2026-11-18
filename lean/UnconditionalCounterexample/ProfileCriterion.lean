import UnconditionalCounterexample.LowOrderBounds
import UnconditionalCounterexample.ConductorAtomicity

/-!
# From actual valuation profiles to hereditary atomicity

The order-one sequence has the specified primary profiles and no outside
support. Coordinatewise divisibility and eventual primary stabilization then
make every sufficiently late member divide each element of horizontal order
at least two. The final theorem combines this with the proved low-order
bounds and conductor induction. All realization and integer-conductor inputs
remain explicit.
-/

namespace UnconditionalCounterexample

universe u v

variable {R : Type u} {ι : Type v} [CommRing R] [IsDomain R]

namespace ValuationProfiles

/-- Any sufficiently late element with the primary profile of `a_n` divides
an actual nonzero top whose horizontal order is at least two. -/
theorem eventually_dvd_of_primaryAtomProfiles
    (v : ValuationProfiles R ι)
    (hdivisibility : ∀ x y : R, x ≠ 0 → y ≠ 0 →
      (∀ p, v.value p x ≤ v.value p y) → x ∣ y)
    (a : ℕ → R) (ha : ∀ n, a n ≠ 0)
    (halimit : ∀ n, v.value .limit (a n) = 1)
    (haoutside : ∀ n i, v.value (.outside i) (a n) = 0)
    (haprimary : ∀ n j, (v.value (.primary j) (a n) : ℤ) = primaryAtomProfile n j)
    {x : R} (hx : x ≠ 0) (hlimit : 2 ≤ v.value .limit x) :
    ∃ N : ℕ, ∀ n ≥ N, a n ∣ x := by
  obtain ⟨N, hN⟩ := v.eventually_primary x hx
  refine ⟨N, ?_⟩
  intro n hn
  apply hdivisibility (a n) x (ha n) hx
  intro p
  cases p with
  | limit =>
      rw [halimit]
      omega
  | outside i =>
      rw [haoutside]
      exact Nat.zero_le _
  | primary j =>
      have hle : (v.value (.primary j) (a n) : ℤ) ≤
          (v.value (.primary j) x : ℤ) := by
        rw [haprimary]
        by_cases hj : j < 2 * n
        · rw [primaryAtomProfile_of_lt hj]
          exact Int.natCast_nonneg _
        · rw [hN j (by omega)]
          unfold primaryAtomProfile
          split_ifs <;> omega
      exact_mod_cast hle

end ValuationProfiles

/-- The valuation laws give the low-order bound and late divisibility. Together with the
integer conductors and sequence congruences these imply hereditary atomicity. -/
theorem hereditarilyAtomic_of_profiles_and_integerConductors
    (v : ValuationProfiles R ι)
    (hdivisibility : ∀ x y : R, x ≠ 0 → y ≠ 0 →
      (∀ p, v.value p x ≤ v.value p y) → x ∣ y)
    (hsigns : ∀ x : R, IsUnit x → x = 1 ∨ x = -1)
    (a : ℕ → R) (ha : ∀ n, a n ≠ 0)
    (halimit : ∀ n, v.value .limit (a n) = 1)
    (haoutside : ∀ n i, v.value (.outside i) (a n) = 0)
    (haprimary : ∀ n j, (v.value (.primary j) (a n) : ℤ) = primaryAtomProfile n j)
    (hcongr : ∀ m : ℕ, 0 < m → ∀ N : ℕ,
      ∃ n ≥ N, (m : R) ∣ a n - 1)
    (hconductors : ∀ T : Subring R, ¬ Factorization.IsBFDomain T →
      ∃ m : ℕ, 0 < m ∧ ∀ z : R, (m : R) * z ∈ T) :
    Factorization.IsHereditarilyAtomic R := by
  apply hereditarilyAtomic_of_integerConductors hsigns
    (fun x => v.value .limit x)
    (fun x y hx hy => v.value_mul .limit x y hx hy)
    (fun x hx hlimit => v.hasBoundedFactorizations_of_limit_le_one hx hlimit)
    a halimit
    (fun x hx hlimit => v.eventually_dvd_of_primaryAtomProfiles
      hdivisibility a ha halimit haoutside haprimary hx hlimit)
    hcongr hconductors

end UnconditionalCounterexample
