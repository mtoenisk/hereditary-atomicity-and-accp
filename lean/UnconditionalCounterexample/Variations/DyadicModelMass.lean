import UnconditionalCounterexample.Variations.DyadicBulkInputs

/-!
# Primitive integral calibration gives the rational horizontal mass

Changing a horizontal polynomial by a rational scalar shifts the primary and
guard orders at each paired fibre by exactly the same integer. Thus the
signed mass of the monic rational horizontal equals that of its primitive
integral model, including at the preexisting primes of the scalar.
-/

noncomputable section
namespace UnconditionalCounterexample.Variations.DyadicLedger

open Polynomial GuardSupport Univariate FreezingCalendar Calibration DyadicDeviations

namespace Driver
variable (D : Driver)

/-- Every listed role of the actual ledger comes from one of its requested
paired fibres, with its transcendental primary still present. -/
theorem paired_of_role {n : ℕ} (p : PrimeIndex) {r : FibreRole}
    (hr : (D.state n).role p = some r) : (permanentSite D.requirements p).paired := by
  induction n with
  | zero => contradiction
  | succ n ih =>
    by_cases h : p ∈ (D.actualRequest n).births.primes
    · obtain ⟨hs,hrole⟩ := D.permanent_role p h
      rw [hs, (D.actualRequest n).paired, ← hrole (n+1) (Nat.lt_succ_self _), hr]
      rfl
    · have eq : (D.state (n+1)).role p = (D.state n).role p := by
        rw [D.state_succ]
        simp [Request.update,Request.nextRole,h]
      exact ih (eq.symm.trans hr)

def rationalOrder (n : ℕ) (f : ℚ[X]) (b : Bool) (p : PrimeIndex) : ℤ :=
  if h : p ∈ ((chain D.requirements).approx n).state.assignment.primes then
    (aeval ((table D.requirements n p h).branch b) f).valuation else 0

/-- Both inputs use the very same table and horizontal height. -/
def rationalMass (n : ℕ) (f : ℚ[X]) (height : Bool → ℤ) (k : Bool) : ℚ :=
  (provisionalProfile ((chain D.requirements).approx n).state.assignment.primes
    (D.state n).role height (D.rationalOrder n f false) (D.rationalOrder n f true)
    (0 : Unit →₀ ℤ)).signedMass (auxWeight (D.state n).role) (auxSign (D.state n).role) k

/-- Divisors of the scalar content are allowed among the old prime sites. -/
theorem rationalMass_eq_model (n : ℕ) (f : Horizontal) (height : Bool → ℤ) (k : Bool) :
    D.rationalMass n f.val height k = D.provisionalMass n (BulkInputs.model f).poly height k := by
  simp only [rationalMass, provisionalMass, tableProfile, provisional_signedMass]
  congr 1
  apply Finset.sum_congr rfl
  intro p hp
  cases hr : (D.state n).role p with
  | none => rfl
  | some r =>
    let T := table D.requirements n p hp
    have hpaired : T.paired := by
      dsimp only [T]
      rw [table_eq_permanentSite]
      exact D.paired_of_role p hr
    let s := ((BulkInputs.model f).scalar : ℚ_[p.val])
    have hs : s ≠ 0 := Rat.cast_ne_zero.mpr (BulkInputs.model f).scalar_ne
    have shifted (b : Bool) : tableOrder (table D.requirements n) (BulkInputs.model f).poly b p =
        D.rationalOrder n f.val b p + s.valuation := by
      have ht := T.branch_transcendental b (Or.inr hpaired)
      have hne : aeval (T.branch b) f.val ≠ 0 := mt ((transcendental_iff.mp ht) f.val) f.property.1.ne_zero
      simp only [tableOrder,rationalOrder,hp,↓reduceDIte]
      rw [BulkInputs.model_eval, Padic.valuation_mul hs hne, add_comm]
    rw [shifted,shifted]
    let u := D.rationalOrder n f.val false p
    let v := D.rationalOrder n f.val true p
    change r.contribution k (u - forecastOrder height (some r)) v =
      r.contribution k (u + _ - forecastOrder height (some r)) (v + _)
    rw [show u + s.valuation - forecastOrder height (some r) =
        (u - forecastOrder height (some r)) + s.valuation by omega,
      r.contribution_add, r.contribution_same, add_zero]

end Driver
end UnconditionalCounterexample.Variations.DyadicLedger
