import UnconditionalCounterexample.SparsePrimaryDomain
import Mathlib.Data.Nat.PrimeFin

/-! Local return estimates at every retained primary and every guard imply
actual integer divisibility in the sparse intersection. -/

noncomputable section
namespace UnconditionalCounterexample.SparsePrimaryDomain
open Filter GuardSupport Polynomial

local instance : Algebra ℚ (RatFunc ℚ) := RatFunc.instAlgebraOfPolynomial ℚ ℚ

def primeAt (d : Places) : ℕ ⊕ PrimeIndex → PrimeIndex
  | .inl j => d.primes j
  | .inr p => p

def evaluationAt (d : Places) (v : ℕ ⊕ PrimeIndex) : RatFunc ℚ →+* ℚ_[(primeAt d v).val] :=
  match v with
  | .inl j => EvaluationDVR.evaluationHom _ (d.primary j).val (d.primary_trans j)
  | .inr p => guardEvaluation d.guard d.guard_trans p

theorem vertical_eq_evaluationAt (d : Places) (v : ℕ ⊕ PrimeIndex) :
    vertical d v = EvaluationDVR.valuation (primeAt d v).val (evaluationAt d v) := by
  cases v <;> rfl

theorem mem_domain_iff_evaluations (d : Places) (S : Set ℚ[X]) (x : RatFunc ℚ) :
    x ∈ domain S d ↔ x ∈ PoleAlgebra.generated S ∧
      ∀ v, evaluationAt d v x ∈ PadicInt.subring (primeAt d v).val := by
  rw [IntersectionDomain.mem_intersection]
  apply and_congr Iff.rfl
  apply forall_congr'
  intro v
  rw [vertical_eq_evaluationAt]
  exact EvaluationDVR.mem_valuationSubring _ _ x

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

theorem finite_places_over_modulus (d : Places) (m : ℕ) :
    {v | (primeAt d v).val ∈ m.primeFactors}.Finite := by
  have hi : {j | (d.primes j).val ∈ m.primeFactors}.Finite :=
    m.primeFactors.finite_toSet.preimage
      (Subtype.val_injective.comp d.primes.injective).injOn
  have hp : {p : PrimeIndex | p.val ∈ m.primeFactors}.Finite :=
    m.primeFactors.finite_toSet.preimage Subtype.val_injective.injOn
  apply ((hi.image (Sum.inl (β := PrimeIndex))).union (hp.image (Sum.inr (α := ℕ)))).subset
  rintro (j | p) h
  · exact Or.inl ⟨j, h, rfl⟩
  · exact Or.inr ⟨p, h, rfl⟩

/-- No omitted primary is needed: the finite tests use the actual sum of the
retained-primary indices and all rational-prime guards. -/
theorem eventually_integer_dvd_sub_one (d : Places) (S : Set ℚ[X]) (a : ℕ → domain S d)
    (hlocal : ∀ v k, ∀ᶠ n in atTop,
      (evaluationAt d v (a n : RatFunc ℚ) - 1) / ((primeAt d v).val : ℚ_[(primeAt d v).val]) ^ k
        ∈ PadicInt.subring (primeAt d v).val) (m : ℕ) (hm : 0 < m) :
    ∀ᶠ n in atTop, (m : domain S d) ∣ a n - 1 := by
  have hfinite := (eventually_all_finite (finite_places_over_modulus d m)).mpr
    (fun v _ => hlocal v (padicValNat (primeAt d v).val m))
  filter_upwards [hfinite] with n hn
  let z : RatFunc ℚ := ((a n : RatFunc ℚ) - 1) / (m : RatFunc ℚ)
  have hz : z ∈ domain S d := by
    apply (mem_domain_iff_evaluations d S z).mpr
    obtain ⟨haB, hab⟩ := (mem_domain_iff_evaluations d S _).mp (a n).property
    constructor
    · change ((a n : RatFunc ℚ) - 1) / m ∈ PoleAlgebra.generated S
      rw [div_eq_mul_inv]
      apply (PoleAlgebra.generated S).mul_mem
        ((PoleAlgebra.generated S).sub_mem haB (PoleAlgebra.generated S).one_mem)
      simpa using (PoleAlgebra.generated S).algebraMap_mem ((m : ℚ)⁻¹)
    · intro v
      let p := (primeAt d v).val
      change evaluationAt d v (((a n : RatFunc ℚ) - 1) / m) ∈ _
      simp only [map_div₀, map_sub, map_one, map_natCast]
      by_cases hp : p ∣ m
      · exact div_natCast_integral_of_precision p m _ hm.ne' le_rfl
          (hn v ((primeAt d v).property.mem_primeFactors hp hm.ne'))
      · apply div_natCast_integral_of_precision p m 0 hm.ne'
          (by simp [padicValNat.eq_zero_of_not_dvd hp])
        simpa using (PadicInt.subring p).sub_mem (hab v) (PadicInt.subring p).one_mem
  refine ⟨⟨z, hz⟩, Subtype.ext ?_⟩
  change (a n : RatFunc ℚ) - 1 = (m : RatFunc ℚ) * (((a n : RatFunc ℚ) - 1) / m)
  field_simp [hm.ne']

theorem eventually_integer_dvd_of_refined_returns (d : Places) (S : Set ℚ[X])
    (a : ℕ → domain S d)
    (hreturn : ∀ v, ∀ᶠ n in atTop,
      (evaluationAt d v (a (n + 1) : RatFunc ℚ) - 1) /
        ((primeAt d v).val : ℚ_[(primeAt d v).val]) ^ n ∈ PadicInt.subring (primeAt d v).val)
    (m : ℕ) (hm : 0 < m) : ∀ᶠ n in atTop, (m : domain S d) ∣ a n - 1 := by
  apply eventually_integer_dvd_sub_one d S a _ m hm
  intro v k
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hreturn v)
  apply eventually_atTop.mpr
  refine ⟨max N k + 1, fun n hn => ?_⟩
  obtain ⟨i, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show n ≠ 0 by omega)
  let p := (primeAt d v).val
  have hp : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr (primeAt d v).property.ne_zero
  have hpi : (p : ℚ_[p]) ∈ PadicInt.subring p := by
    change ‖(p : ℚ_[p])‖ ≤ 1
    simpa only [Int.cast_natCast] using (Padic.norm_int_le_one (p := p) (p : ℤ))
  have hi := hN i (by omega)
  obtain ⟨l, rfl⟩ := Nat.exists_eq_add_of_le (show k ≤ i by omega)
  convert (PadicInt.subring p).mul_mem hi ((PadicInt.subring p).pow_mem hpi l) using 1
  change _ / (p : ℚ_[p]) ^ k = _ / (p : ℚ_[p]) ^ (k+l) * _
  rw [pow_add]
  field_simp

end UnconditionalCounterexample.SparsePrimaryDomain
