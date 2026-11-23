import UnconditionalCounterexample.Variations.DyadicLedger
import UnconditionalCounterexample.EvaluationChoices

/-!
# Values of dyadic raws at all permanent vertical sites

The stage-specific integer column and unit multiplier fix the exact order on
the processed fibre. Screening proves the complementary case of a primary born
later. The normalized raw is a unit at every guard at every prime.
-/

namespace UnconditionalCounterexample.Variations.DyadicLedger.Driver

open GuardSupport PrimaryChoices RecursivePrefix Univariate MixedStageSelection

variable (D : Driver)

private theorem norm_unit_factor {p : ℕ} [Fact p.Prime] (u : ℤ_[p]ˣ) : ‖u.val.val‖ = 1 :=
  PadicInt.isUnit_iff.mp u.isUnit

theorem generator_guard_norm_one (n : ℕ) (p : PrimeIndex) :
    ‖(permanentSite D.requirements p).evaluate true (Or.inl rfl) ((chain D.requirements).generators n)‖ = 1 := by
  apply generator_guard_norm
  intro raw i
  rw [D.actualTarget_value]
  simp

private theorem processed_of_birth {birth n : ℕ} {p : PrimeIndex}
    (hp : p ∈ (D.actualRequest birth).births.primes) (hle : birth ≤ n) :
    p ∈ (selection D.requirements n).batch.processed.primes := by
  have h := D.schedule.requested_processed birth hp
  rcases eq_or_lt_of_le hle with rfl | hlt
  · exact h
  · rw [(selection D.requirements n).progress.processed]
    exact Finset.mem_union_left _ (Finset.mem_union_left _ (assigned_mono D.requirements hlt
      ((selection D.requirements birth).batch.processed_subset_assigned h)))

private theorem target_norm (n : ℕ) (j : (selection D.requirements n).batch.indices) :
    ‖(actualTargets D.requirements n).value j false‖ =
      ‖((primes j.val).val : ℚ_[(primes j.val).val]) ^ ((D.actualRequest n).column.atPrimary
        (primes j.val) ((D.actualRequest n).nextRole (primes j.val)))‖ := by
  rw [D.actualTarget_value, norm_mul, norm_unit_factor, mul_one]
  rfl

/-- Exact order at a primary born at any stage. Its earlier raw factors have
order zero. All generators from the birth stage onwards have their declared
signed order, including the value -1 in an adjacent column. -/
theorem generator_primary_order (n birth : ℕ) (p : PrimeIndex)
    (hp : p ∈ (D.actualRequest birth).births.primes)
    (hpair : ((D.actualRequest birth).births.site p hp).paired) :
    ((permanentSite D.requirements p).evaluate false (Or.inr (by
      rwa [D.schedule.permanentSite_requested birth p hp])) ((chain D.requirements).generators n)).valuation =
      if n < birth then 0 else (D.actualRequest n).column.atPrimary p ((D.actualRequest birth).role p hp) := by
  let x := (chain D.requirements).generators n
  have hPa : Active (permanentSite D.requirements p).paired false :=
    Or.inr (by rwa [D.schedule.permanentSite_requested birth p hp])
  let y := (permanentSite D.requirements p).evaluate false hPa x
  have hy : y ≠ 0 := (map_ne_zero _).mpr ((chain D.requirements).generators_ne_zero n)
  change y.valuation = _
  by_cases h : n < birth
  · rw [ite_eq_left h]
    have hnorm := generator_norm_before_birth D.schedule p hp hpair
      ((D.actualRequest birth).primary_before p hp hpair) n h
    simpa using EvaluationChoices.valuation_eq_of_norm_eq p.val hy (one_ne_zero : (1 : ℚ_[p.val]) ≠ 0)
      (hnorm.trans norm_one.symm)
  · rw [ite_eq_right h]
    let z := (D.actualRequest n).column.atPrimary p ((D.actualRequest birth).role p hp)
    have hpz : (p.val : ℚ_[p.val]) ^ z ≠ 0 := zpow_ne_zero _ (Nat.cast_ne_zero.mpr p.property.ne_zero)
    have hrole : (D.actualRequest n).nextRole p = (D.actualRequest birth).role p hp := by
      have h₁ := D.role_persistent p hp (show birth < n+1 by omega)
      rwa [D.state_succ] at h₁
    have hnorm (j : ℕ) (hj : primes j = p)
        (hm : p ∈ (selection D.requirements n).batch.processed.primes) :
        ‖y‖ = ‖(p.val : ℚ_[p.val]) ^ z‖ := by
      subst p
      let B := (selection D.requirements n).batch
      let i : B.indices := ⟨j, (B.mem_indices j).mpr hm⟩
      have hd := (processed_value D.requirements n i false hPa).1.trans (D.target_norm n i)
      change ‖y‖ = ‖((primes j).val : ℚ_[(primes j).val]) ^
        (D.actualRequest n).column.atPrimary (primes j) ((D.actualRequest n).nextRole (primes j))‖ at hd
      rw [hrole] at hd
      exact hd
    obtain ⟨j, hj⟩ := primes.surjective p
    rw [EvaluationChoices.valuation_eq_of_norm_eq p.val hy hpz
      (hnorm j hj (D.processed_of_birth hp (by omega))), Padic.valuation_zpow, Padic.valuation_p, mul_one]

end UnconditionalCounterexample.Variations.DyadicLedger.Driver
