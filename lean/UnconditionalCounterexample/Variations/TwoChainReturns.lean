import UnconditionalCounterexample.Variations.UnivariateRecovery
import Mathlib.Data.Nat.PrimeFin

/-!
# Integer returns in the actual univariate intersection

Only the one or two selected points above primes dividing the modulus need
a local return estimate. At other primes the integer denominator is a unit.
-/

noncomputable section
namespace UnconditionalCounterexample.Variations.Univariate

open GuardSupport UnivariateConductor Filter Polynomial

local instance : Algebra ℚ (RatFunc ℚ) := RatFunc.instAlgebraOfPolynomial ℚ ℚ

/-- A residue condition modulo a sufficiently large prime power allows division
by the given integer in the local integer ring. -/
theorem integral_div_nat_of_precision {p : ℕ} [Fact p.Prime]
    {m n : ℕ} (hm : m ≠ 0) (h : padicValNat p m ≤ n) {z : ℚ_[p]}
    (hz : z / (p : ℚ_[p])^n ∈ PadicInt.subring p) : z / (m : ℚ_[p]) ∈ PadicInt.subring p := by
  have hp : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  have hm' : (m : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr hm
  have hscale : (p : ℚ_[p])^n / (m : ℚ_[p]) ∈ PadicInt.subring p := by
    apply (Padic.norm_le_one_iff_val_nonneg _).mpr
    rw [div_eq_mul_inv, Padic.valuation_mul (pow_ne_zero _ hp) (inv_ne_zero hm'),
      Padic.valuation_inv, Padic.valuation_pow, Padic.valuation_p, Padic.valuation_natCast]
    omega
  convert (PadicInt.subring p).mul_mem hz hscale using 1
  field_simp

/-- The growing return precision at each active branch yields divisibility by
every positive integer in the intersection defined by this same sequence. -/
theorem eventually_dvd_of_branch_returns (R : Requirements) (a : ℕ → domain R)
    (hlocal : ∀ (p : PrimeIndex) (b : Bool) (hb : MixedStageSelection.Active (permanentSite R p).paired b),
      ∀ᶠ n in atTop, (EvaluationDVR.evaluationHom p.val ((permanentSite R p).branch b)
        ((permanentSite R p).branch_transcendental b hb) (a (n+1) : RatFunc ℚ) - 1) /
        (p.val : ℚ_[p.val])^(n+1) ∈ PadicInt.subring p.val)
    (m : ℕ) (hm : 0 < m) : ∀ᶠ n in atTop, (m : domain R) ∣ a n - 1 := by
  have hpoints (p : PrimeIndex) (z : Point p) (hz : z ∈ (permanentSite R p).fibre.points) :
      ∀ᶠ n in atTop, (LocalEvaluation.evalAt z.value.val z.transcendental (a n : RatFunc ℚ) - 1) /
        (m : ℚ_[p.val]) ∈ PadicInt.subring p.val := by
    obtain ⟨b, hb, he⟩ := (permanentSite R p).branch_of_point hz
    obtain ⟨N, hN⟩ := eventually_atTop.mp (hlocal p b hb)
    apply eventually_atTop.mpr
    refine ⟨max N (padicValNat p.val m) + 1, fun n hn => ?_⟩
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show n ≠ 0 by omega)
    apply integral_div_nat_of_precision hm.ne' (n := j+1) (by omega)
    have hret := hN j (by omega)
    change (LocalEvaluation.evalAt _ _ _ - 1) / _ ∈ _ at hret
    simpa only [he] using hret
  let primes : Set PrimeIndex := {p | p.val ∈ m.primeFactors}
  have hfin : primes.Finite := m.primeFactors.finite_toSet.preimage Subtype.val_injective.injOn
  have h := (eventually_all_finite hfin).mpr (fun p _ =>
    (eventually_all_finite (show (permanentSite R p).fibre.points.Finite by
      cases (permanentSite R p).fibre <;> simp [Fibre.points])).mpr (hpoints p))
  filter_upwards [h] with n hn
  have ha := (mem_domain_iff R _).mp (a n).property
  let z : RatFunc ℚ := ((a n : RatFunc ℚ) - 1) / m
  have hz : z ∈ domain R := by
    apply (mem_domain_iff R _).mpr
    constructor
    · change ((a n : RatFunc ℚ)-1) / m ∈ poleAlgebra R
      rw [div_eq_mul_inv]
      apply (poleAlgebra R).mul_mem ((poleAlgebra R).sub_mem ha.1 (poleAlgebra R).one_mem)
      simpa using (poleAlgebra R).algebraMap_mem ((m : ℚ)⁻¹)
    · intro p q hq
      simp only [z, map_div₀, map_sub, map_one, map_natCast]
      by_cases hd : p.val ∣ m
      · exact hn p (p.property.mem_primeFactors hd hm.ne') q hq
      · apply integral_div_nat_of_precision hm.ne' (n := 0) (by simp [padicValNat.eq_zero_of_not_dvd hd])
        simpa using (PadicInt.subring p.val).sub_mem (ha.2 p q hq) (PadicInt.subring _).one_mem
  refine ⟨⟨z, hz⟩, Subtype.ext ?_⟩
  change (a n : RatFunc ℚ) - 1 = (m : RatFunc ℚ) * (((a n : RatFunc ℚ) - 1) / m)
  field_simp [hm.ne']

end UnconditionalCounterexample.Variations.Univariate
