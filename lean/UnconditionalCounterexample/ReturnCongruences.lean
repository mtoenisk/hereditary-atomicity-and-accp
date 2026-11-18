import UnconditionalCounterexample.PairedDomain
import Mathlib.Data.Nat.PrimeFin

/-!
# From the local refined return to divisibility in D

At a q-stage the estimate for a_(n+1) has precision p^n. Only the finitely
many primes dividing a positive modulus m impose a condition. At every other
prime the element is integral and the denominator m is a unit. Testing the
explicit quotient (a_(n+1) - 1)/m in the defining intersection proves the last
assertion of Proposition 3.1(1) from these local returns.
-/

noncomputable section
namespace UnconditionalCounterexample.PairedDomain

open Filter GuardSupport Polynomial

local instance : Algebra ℚ (RatFunc ℚ) := RatFunc.instAlgebraOfPolynomial ℚ ℚ

private theorem div_natCast_integral_of_precision (p m n : ℕ) [Fact p.Prime]
    (hm : m ≠ 0) (hn : padicValNat p m ≤ n) {z : ℚ_[p]}
    (hz : z / (p : ℚ_[p]) ^ n ∈ PadicInt.subring p) :
    z / (m : ℚ_[p]) ∈ PadicInt.subring p := by
  have hp : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  have hm' : (m : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr hm
  have hscale : (p : ℚ_[p]) ^ n / (m : ℚ_[p]) ∈ PadicInt.subring p := by
    apply (Padic.norm_le_one_iff_val_nonneg _).mpr
    rw [div_eq_mul_inv, Padic.valuation_mul (pow_ne_zero _ hp) (inv_ne_zero hm'),
      Padic.valuation_inv, Padic.valuation_pow, Padic.valuation_p, Padic.valuation_natCast]
    omega
  convert (PadicInt.subring p).mul_mem hz hscale using 1
  field_simp

/-- The two evaluations above a rational prime, in primary/guard order. -/
def evaluationBranch (d : Places) (j : ℕ) (b : Bool) : RatFunc ℚ →+* ℚ_[(d.primes j).val] :=
  if b then guardEvaluation d.guard d.guard_trans (d.primes j) else
    EvaluationDVR.evaluationHom (d.primes j).val (d.primary j).val (d.primary_trans j)

/-- Read membership in the actual intersection at the two branches above each prime. -/
theorem mem_domain_iff_branches (d : Places) (S : Set ℚ[X]) (x : RatFunc ℚ) :
    x ∈ domain S d ↔ x ∈ PoleAlgebra.generated S ∧
      ∀ (j : ℕ) (b : Bool), evaluationBranch d j b x ∈ PadicInt.subring (d.primes j).val := by
  rw [IntersectionDomain.mem_intersection]
  constructor
  · rintro ⟨hB, h⟩
    refine ⟨hB, fun j b => ?_⟩
    cases b with
    | false => exact (EvaluationDVR.mem_valuationSubring _ _ x).mp (h (.inl j))
    | true => exact (EvaluationDVR.mem_valuationSubring _ _ x).mp (h (.inr (d.primes j)))
  · rintro ⟨hB, h⟩
    refine ⟨hB, ?_⟩
    rintro (j | p)
    · exact (EvaluationDVR.mem_valuationSubring _ _ x).mpr (h j false)
    · obtain ⟨j, rfl⟩ := d.primes.surjective p
      exact (EvaluationDVR.mem_valuationSubring _ _ x).mpr (h j true)

/-- Integral return at the two branches over each fixed prime, with arbitrarily
large precision, gives eventual divisibility inside D for every integer modulus. -/
theorem eventually_integer_dvd_sub_one (d : Places) (S : Set ℚ[X]) (a : ℕ → domain S d)
    (hlocal : ∀ (j k : ℕ) (b : Bool), ∀ᶠ n in atTop,
      (evaluationBranch d j b (a n : RatFunc ℚ) - 1) / ((d.primes j).val : ℚ_[(d.primes j).val]) ^ k
        ∈ PadicInt.subring (d.primes j).val) (m : ℕ) (hm : 0 < m) :
    ∀ᶠ n in atTop, (m : domain S d) ∣ a n - 1 := by
  let I : Set ℕ := {j | (d.primes j).val ∈ m.primeFactors}
  have hI : I.Finite := m.primeFactors.finite_toSet.preimage
    (Subtype.val_injective.comp d.primes.injective).injOn
  have hfinite := (eventually_all_finite hI).mpr (fun j _ =>
    (eventually_all).mpr (fun b => hlocal j (padicValNat (d.primes j).val m) b))
  filter_upwards [hfinite] with n hn
  let z : RatFunc ℚ := ((a n : RatFunc ℚ) - 1) / (m : RatFunc ℚ)
  have hz : z ∈ domain S d := by
    apply (mem_domain_iff_branches d S z).mpr
    obtain ⟨haB, hab⟩ := (mem_domain_iff_branches d S _).mp (a n).property
    constructor
    · change ((a n : RatFunc ℚ) - 1) / m ∈ PoleAlgebra.generated S
      rw [div_eq_mul_inv]
      apply (PoleAlgebra.generated S).mul_mem ((PoleAlgebra.generated S).sub_mem haB (PoleAlgebra.generated S).one_mem)
      simpa using (PoleAlgebra.generated S).algebraMap_mem ((m : ℚ)⁻¹)
    · intro j b
      let p := (d.primes j).val
      change evaluationBranch d j b (((a n : RatFunc ℚ) - 1) / m) ∈ _
      simp only [map_div₀, map_sub, map_one, map_natCast]
      by_cases hp : p ∣ m
      · exact div_natCast_integral_of_precision p m _ hm.ne' le_rfl
          (hn j ((d.primes j).property.mem_primeFactors hp hm.ne') b)
      · apply div_natCast_integral_of_precision p m 0 hm.ne'
          (by simp [padicValNat.eq_zero_of_not_dvd hp])
        simpa using (PadicInt.subring p).sub_mem (hab j b) (PadicInt.subring p).one_mem
  refine ⟨⟨z, hz⟩, Subtype.ext ?_⟩
  change (a n : RatFunc ℚ) - 1 = (m : RatFunc ℚ) * (((a n : RatFunc ℚ) - 1) / m)
  field_simp [hm.ne']

/-- The refined q-stage return has precision n on a_(n+1). It suffices
at each fixed branch, since n and the construction stage tend to infinity. -/
theorem eventually_integer_dvd_of_refined_returns (d : Places) (S : Set ℚ[X])
    (a : ℕ → domain S d)
    (hreturn : ∀ (j : ℕ) (b : Bool), ∀ᶠ n in atTop,
      (evaluationBranch d j b (a (n + 1) : RatFunc ℚ) - 1) /
          ((d.primes j).val : ℚ_[(d.primes j).val]) ^ n ∈ PadicInt.subring (d.primes j).val)
    (m : ℕ) (hm : 0 < m) : ∀ᶠ n in atTop, (m : domain S d) ∣ a n - 1 := by
  apply eventually_integer_dvd_sub_one d S a _ m hm
  intro j k b
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hreturn j b)
  apply eventually_atTop.mpr
  refine ⟨max N k + 1, fun n hn => ?_⟩
  obtain ⟨i, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show n ≠ 0 by omega)
  let p := (d.primes j).val
  have hp : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr (d.primes j).property.ne_zero
  have hpi : (p : ℚ_[p]) ∈ PadicInt.subring p := by
    change ‖(p : ℚ_[p])‖ ≤ 1
    simpa only [Int.cast_natCast] using (Padic.norm_int_le_one (p := p) (p : ℤ))
  have hi := hN i (by omega)
  obtain ⟨l, rfl⟩ := Nat.exists_eq_add_of_le (show k ≤ i by omega)
  convert (PadicInt.subring p).mul_mem hi ((PadicInt.subring p).pow_mem hpi l) using 1
  change _ / (p : ℚ_[p]) ^ k = _ / (p : ℚ_[p]) ^ (k+l) * _
  rw [pow_add]
  field_simp

end UnconditionalCounterexample.PairedDomain
