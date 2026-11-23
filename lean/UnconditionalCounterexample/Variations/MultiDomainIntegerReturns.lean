import UnconditionalCounterexample.Variations.MultiDomainLocalReturns
import UnconditionalCounterexample.Variations.MultiDomainLocalization

/-!
# Integer returns in the multivariate intersection and at the extra point

At the finitely many components above divisors of m, the return precision
eventually exceeds the local order of m. At all other components m is a
unit. This proves divisibility in the ordinary ring and the extra integrality
needed by the rational-point pullback.
-/

noncomputable section
namespace UnconditionalCounterexample.Variations.MultiDomain

open Filter GuardSupport WithZero IntersectionDomain IsLocalRing

theorem unit_nat_of_coprime {K : Type*} [Field K] (v : Valuation K ℤᵐ⁰) (p : PrimeIndex)
    (hp : v (p.val : K) = exp (-1)) (m : ℕ) (hm : ¬ p.val ∣ m) : v (m : K) = 1 := by
  let V := v.valuationSubring
  let k := ResidueField V
  have hz (n : ℕ) : (n : k) = 0 ↔ v (n : K) < 1 := by
    rw [← map_natCast (residue V), residue_eq_zero_iff]
    exact Valuation.mem_maximalIdeal_iff K v
  let : CharP k p.val := (CharP.charP_iff_prime_eq_zero p.property).mpr
    ((hz p.val).mpr (by rw [hp, exp_lt_one_iff]; decide))
  exact (valuation_natCast_le_one v m).antisymm (le_of_not_gt fun h ↦
    hm ((CharP.cast_eq_zero_iff k p.val m).mp ((hz m).mpr h)))

theorem eventually_div_integer {K : Type*} [Field K] [CharZero K] (v : Valuation K ℤᵐ⁰)
    (p : PrimeIndex) (hp : v (p.val : K) = exp (-1)) (x : ℕ → K)
    (hx : ∀ᶠ n in atTop, v (x n / (p.val : K)^n) ≤ 1) (m : ℕ) (hm : 0 < m) :
    ∀ᶠ n in atTop, v (x n / (m : K)) ≤ 1 := by
  have hmp : (m : K) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  have hpp : (p.val : K) ≠ 0 := Nat.cast_ne_zero.mpr p.property.ne_zero
  filter_upwards [hx, eventually_ge_atTop (-log (v (m : K))).toNat] with n hn hge
  rw [map_div₀, div_le_one₀ (v.pos_iff.mpr (pow_ne_zero _ hpp)), map_pow, hp, ← exp_nsmul] at hn
  rw [map_div₀, div_le_one₀ (v.pos_iff.mpr hmp), ← exp_log (v.ne_zero_iff.mpr hmp)]
  exact hn.trans (exp_le_exp.mpr (by simp only [nsmul_eq_mul, mul_neg, mul_one]; omega))

variable {r : ℕ} {A : Data r}

/-- The full local list has one guard per rational prime and at most one
primary over it. Only finitely many primes need a return estimate for m. -/
theorem ordinary_integer_return (H : Clearing A) (hinj : Function.Injective H.primes)
    (a : ℕ → ordinary A)
    (hp : ∀ j, ∀ᶠ n in atTop, A.primary j (((a n : FunctionField r)-1) / ((H.primes j).val : FunctionField r)^n) ≤ 1)
    (hg : ∀ p, ∀ᶠ n in atTop, A.guard p (((a n : FunctionField r)-1) / (p.val : FunctionField r)^n) ≤ 1)
    (m : ℕ) (hm : 0 < m) : ∀ᶠ n in atTop, (m : ordinary A) ∣ a n - 1 := by
  let primes : ℕ ⊕ PrimeIndex → PrimeIndex := Sum.elim H.primes id
  have hpi (i) : vertical A i ((primes i).val : FunctionField r) = exp (-1) := by
    cases i with | inl j => exact H.primary_prime j | inr p => exact H.guard_prime p
  have hfin : {i | (primes i).val ∈ m.primeFactors}.Finite := by
    apply Set.finite_preimage_inl_and_inr.mp
    change ((Subtype.val ∘ H.primes) ⁻¹' (m.primeFactors : Set ℕ)).Finite ∧
      ((Subtype.val : PrimeIndex → ℕ) ⁻¹' (m.primeFactors : Set ℕ)).Finite
    exact ⟨m.primeFactors.finite_toSet.preimage (Subtype.val_injective.comp hinj).injOn,
      m.primeFactors.finite_toSet.preimage Subtype.val_injective.injOn⟩
  have hall (i : ℕ ⊕ PrimeIndex) :
      ∀ᶠ n in atTop, vertical A i (((a n : FunctionField r)-1)/(m : FunctionField r)) ≤ 1 := by
    apply eventually_div_integer _ (primes i) (hpi i) _ _ m hm
    cases i with | inl j => exact hp j | inr p => exact hg p
  filter_upwards [(eventually_all_finset hfin.toFinset).mpr (fun i _ ↦ hall i)] with n hn
  apply (subring_dvd_iff_div_mem _ _ _ (Nat.cast_ne_zero.mpr hm.ne')).mpr
  apply (mem_intersection _ _ _).mpr
  constructor
  · have h1 : ((m : FunctionField r))⁻¹ ∈ poleAlgebra A := by
      have := ((poleAlgebra A).restrictScalars ℚ).algebraMap_mem (m : ℚ)⁻¹
      simpa only [map_inv₀, map_natCast, Subalgebra.mem_restrictScalars] using this
    change (((a n : FunctionField r)-1)/(m : FunctionField r)) ∈ poleAlgebra A
    rw [div_eq_mul_inv]
    exact (poleAlgebra A).mul_mem (ordinary_le_pole (a n - 1).property) h1
  · intro i
    by_cases hi : (primes i).val ∣ m
    · exact hn i (hfin.mem_toFinset.mpr ((primes i).property.mem_primeFactors hi hm.ne'))
    · change vertical A i (((a n : FunctionField r)-1)/(m : FunctionField r)) ≤ 1
      rw [map_div₀, unit_nat_of_coprime _ _ (hpi i) m hi, div_one]
      exact ((mem_intersection _ _ _).mp (a n - 1).property).2 i

theorem mem_localRationals_iff (p : PrimeIndex) (x : ℚ) :
    x ∈ PointPullback.localRationals p.val ↔ Padic.mulValuation (x : ℚ_[p.val]) ≤ 1 := by
  change ‖(x : ℚ_[p.val])‖ ≤ 1 ↔ Padic.mulValuation (x : ℚ_[p.val]) ≤ 1
  simpa only [not_lt, norm_one, map_one] using not_congr
    (Padic.norm_lt_norm_iff_mulValuation_lt (x := (1 : ℚ_[p.val])) (y := (x : ℚ_[p.val])))

theorem rational_point_unit (p : PrimeIndex) {x : ℚ} (hv : Padic.mulValuation (x : ℚ_[p.val]) = 1) :
    ∃ u : (PointPullback.localRationals p.val)ˣ,
      ((u : PointPullback.localRationals p.val) : ℚ) = x := by
  have h0 : x ≠ 0 := by rintro rfl; simp at hv
  have hi : x⁻¹ ∈ PointPullback.localRationals p.val :=
    (mem_localRationals_iff p _).mpr (by simp [hv])
  exact ⟨⟨⟨x,(mem_localRationals_iff p _).mpr hv.le⟩, ⟨x⁻¹,hi⟩,
    Subtype.ext (mul_inv_cancel₀ h0), Subtype.ext (inv_mul_cancel₀ h0)⟩, rfl⟩

theorem rational_point_integer_return (p : PrimeIndex) (a : ℕ → ℚ)
    (h : ∀ᶠ n in atTop, Padic.mulValuation (((a n : ℚ_[p.val])-1)/(p.val : ℚ_[p.val])^n) ≤ 1)
    (m : ℕ) (hm : 0 < m) : ∀ᶠ n in atTop, (a n - 1) / m ∈ PointPullback.localRationals p.val := by
  have hp : Padic.mulValuation (p.val : ℚ_[p.val]) = exp (-1) := by
    simpa [EvaluationDVR.valuation] using EvaluationDVR.valuation_prime p.val (RingHom.id ℚ_[p.val])
  filter_upwards [eventually_div_integer _ p hp _ h m hm] with n hn
  exact (mem_localRationals_iff p _).mpr (by simpa using hn)

end UnconditionalCounterexample.Variations.MultiDomain
