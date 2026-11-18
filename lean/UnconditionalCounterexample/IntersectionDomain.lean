import UnconditionalCounterexample.RationalFunctionSubring
import Mathlib.Algebra.Order.GroupWithZero.WithZero
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.RingTheory.Localization.AsSubring
import Lean.Elab.Tactic.Omega

/-!
# The actual intersection and integer localization

The domain is the intersection of the pole algebra with the retained valuation rings
in one field. Membership and divisibility can be tested there. Finite negative support
and normalized integer-valued vertical valuations permit the poles to be cleared by an
integer.
-/

noncomputable section

namespace UnconditionalCounterexample.IntersectionDomain

open WithZero

variable {K ι Γ₀ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ₀]

/-- Intersection inside the specified common field. -/
def intersection (B : Subring K) (v : ι → Valuation K Γ₀) : Subring K :=
  B ⊓ ⨅ i, (v i).valuationSubring.toSubring

@[simp] theorem mem_intersection (B : Subring K) (v : ι → Valuation K Γ₀) (x : K) :
    x ∈ intersection B v ↔ x ∈ B ∧ ∀ i, v i x ≤ 1 := by
  simp [intersection, Valuation.mem_valuationSubring_iff]

theorem intersection_le (B : Subring K) (v : ι → Valuation K Γ₀) :
    intersection B v ≤ B := inf_le_left

theorem div_mem_iff (B : Subring K) (v : ι → Valuation K Γ₀)
    {x y : K} (hx : x ≠ 0) :
    y / x ∈ intersection B v ↔ y / x ∈ B ∧ ∀ i, v i y ≤ v i x := by
  rw [mem_intersection]
  apply and_congr Iff.rfl
  apply forall_congr'
  intro i
  rw [map_div₀, div_le_one₀ ((v i).pos_iff.mpr hx)]

theorem subring_dvd_iff_div_mem (D : Subring K) (x y : D) (hx : x ≠ 0) :
    x ∣ y ↔ (y : K) / (x : K) ∈ D := by
  have hxK : (x : K) ≠ 0 := fun h => hx (Subtype.ext h)
  constructor
  · rintro ⟨z, rfl⟩
    change (x : K) * (z : K) / (x : K) ∈ D
    rw [mul_div_cancel_left₀ _ hxK]
    exact z.property
  · intro h
    refine ⟨⟨(y : K) / (x : K), h⟩, ?_⟩
    apply Subtype.ext
    change (y : K) = (x : K) * ((y : K) / (x : K))
    exact (mul_div_cancel₀ (y : K) hxK).symm

theorem dvd_iff (B : Subring K) (v : ι → Valuation K Γ₀)
    (x y : intersection B v) (hx : x ≠ 0) :
    x ∣ y ↔ (y : K) / (x : K) ∈ B ∧ ∀ i, v i y ≤ v i x := by
  rw [subring_dvd_iff_div_mem _ x y hx]
  exact div_mem_iff B v (fun h => hx (Subtype.ext h))

/-- Natural constants are integral for every nonarchimedean valuation. -/
theorem valuation_natCast_le_one (v : Valuation K Γ₀) (n : ℕ) : v (n : K) ≤ 1 := by
  induction n with
  | zero => simp
  | succ n hn =>
    rw [Nat.cast_add, Nat.cast_one]
    exact (v.map_add _ _).trans (max_le hn (by simp))

/-- A normalized prime supplies a positive integer clearing one discrete valuation. -/
theorem exists_nat_mul_integral (v : Valuation K ℤᵐ⁰) (p : ℕ) (hp : 0 < p)
    (hv : v (p : K) = exp (-1)) (x : K) :
    ∃ n : ℕ, 0 < n ∧ v ((n : K) * x) ≤ 1 := by
  by_cases hx : x = 0
  · exact ⟨1, by decide, by simp [hx]⟩
  let m : ℕ := (log (v x)).toNat
  refine ⟨p ^ m, pow_pos hp _, ?_⟩
  rw [Nat.cast_pow, map_mul, map_pow, hv, ← exp_nsmul,
    ← exp_log (v.ne_zero_iff.mpr hx), ← exp_add]
  have h : -(m : ℤ) + log (v x) ≤ 0 := by
    dsimp [m]
    omega
  apply exp_le_one_iff.mpr
  simpa only [nsmul_eq_mul, mul_neg, mul_one] using h

/-- Finitely many failures of integrality can be cleared simultaneously. -/
theorem exists_nat_mul_integral_of_finite (v : ι → Valuation K Γ₀) (x : K)
    (hfinite : Set.Finite {i | 1 < v i x})
    (hclear : ∀ i, ∃ n : ℕ, 0 < n ∧ v i ((n : K) * x) ≤ 1) :
    ∃ n : ℕ, 0 < n ∧ ∀ i, v i ((n : K) * x) ≤ 1 := by
  classical
  have hfinset : ∀ s : Finset ι, ∃ n : ℕ, 0 < n ∧
      (∀ i ∈ s, v i ((n : K) * x) ≤ 1) := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨1, by decide, by simp⟩
    | @insert i s his ih =>
      obtain ⟨m, hm, hms⟩ := ih
      obtain ⟨n, hn, hni⟩ := hclear i
      refine ⟨m * n, Nat.mul_pos hm hn, ?_⟩
      intro j hj
      rw [Nat.cast_mul]
      rcases Finset.mem_insert.mp hj with rfl | hj
      · rw [mul_assoc, map_mul]
        exact by simpa using mul_le_mul' (valuation_natCast_le_one (v j) m) hni
      · rw [mul_right_comm, map_mul]
        exact by simpa using mul_le_mul' (hms j hj) (valuation_natCast_le_one (v j) n)
  obtain ⟨n, hn, hns⟩ := hfinset hfinite.toFinset
  refine ⟨n, hn, fun i => ?_⟩
  by_cases hi : 1 < v i x
  · exact hns i (hfinite.mem_toFinset.mpr hi)
  · rw [map_mul]
    exact by simpa using mul_le_mul' (valuation_natCast_le_one (v i) n) (le_of_not_gt hi)

/-- Integer clearing uses only finite negative additive support, not finite total support. -/
theorem exists_nat_mul_mem_intersection (B : Subring K) (v : ι → Valuation K ℤᵐ⁰)
    (p : ι → ℕ) (hp : ∀ i, 0 < p i) (hvp : ∀ i, v i (p i : K) = exp (-1))
    (x : K) (hx : x ∈ B) (hfinite : Set.Finite {i | 1 < v i x}) :
    ∃ n : ℕ, 0 < n ∧ (n : K) * x ∈ intersection B v := by
  obtain ⟨n, hn, hnv⟩ := exists_nat_mul_integral_of_finite v x hfinite
    (fun i => exists_nat_mul_integral (v i) (p i) (hp i) (hvp i) x)
  exact ⟨n, hn, (mem_intersection B v _).mpr ⟨B.mul_mem (natCast_mem B n) hx, hnv⟩⟩

/-- The map from the intersection to B is the literal inclusion in the common field. -/
def inclusion (B : Subring K) (v : ι → Valuation K Γ₀) : intersection B v →+* B :=
  Subring.inclusion (intersection_le B v)

instance inclusionAlgebra (B : Subring K) (v : ι → Valuation K Γ₀) :
    Algebra (intersection B v) B := (inclusion B v).toAlgebra

@[simp] theorem coe_algebraMap (B : Subring K) (v : ι → Valuation K Γ₀)
    (x : intersection B v) : ((algebraMap (intersection B v) B x : B) : K) = x := rfl

instance inclusionScalarTower (B : Subring K) (v : ι → Valuation K Γ₀) :
    IsScalarTower (intersection B v) B K :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

/-- The nonzero integers, viewed inside a unital subring. -/
def integerDenominators (D : Subring K) : Submonoid D :=
  (nonZeroDivisors ℤ).map (Int.castRingHom D)

instance subalgebraInclusionAlgebra [Algebra ℚ K] (B : Subalgebra ℚ K)
    (v : ι → Valuation K Γ₀) : Algebra (intersection B.toSubring v) B :=
  inclusionAlgebra B.toSubring v

instance subalgebraInclusionScalarTower [Algebra ℚ K] (B : Subalgebra ℚ K)
    (v : ι → Valuation K Γ₀) : IsScalarTower (intersection B.toSubring v) B K :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

/-- Inverting the nonzero integers recovers B as its actual canonical D-algebra. -/
theorem integer_isLocalization [Algebra ℚ K] (B : Subalgebra ℚ K)
    (v : ι → Valuation K ℤᵐ⁰) (p : ι → ℕ) (hp : ∀ i, 0 < p i)
    (hvp : ∀ i, v i (p i : K) = exp (-1))
    (hfinite : ∀ x ∈ B, Set.Finite {i | 1 < v i x}) :
    IsLocalization (integerDenominators (intersection B.toSubring v)) B := by
  apply (isLocalization_iff _ _).mpr
  refine ⟨?_, ?_, ?_⟩
  · intro s
    obtain ⟨z, hz, hzs⟩ := s.property
    change IsUnit (algebraMap (intersection B.toSubring v) B s.val)
    rw [← hzs]
    have hz0 : z ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hz
    have hzq : IsUnit (z : ℚ) := isUnit_iff_ne_zero.mpr (by exact_mod_cast hz0)
    simpa using hzq.map (algebraMap ℚ B)
  · intro x
    obtain ⟨n, hn, hnx⟩ := exists_nat_mul_mem_intersection B.toSubring v p hp hvp
      x x.property (hfinite x x.property)
    let a : intersection B.toSubring v := ⟨(n : K) * x, hnx⟩
    have hnS : (n : intersection B.toSubring v) ∈
        integerDenominators (intersection B.toSubring v) := by
      refine ⟨(n : ℤ), ?_, by simp⟩
      exact mem_nonZeroDivisors_iff_ne_zero.mpr (by exact_mod_cast Nat.ne_of_gt hn)
    refine ⟨⟨a, ⟨n, hnS⟩⟩, ?_⟩
    apply Subtype.ext
    change (x : K) * n = n * (x : K)
    exact mul_comm _ _
  · intro x y hxy
    refine ⟨1, ?_⟩
    have heq : x = y := by
      apply Subtype.ext
      exact congrArg (fun z : B => (z : K)) hxy
    simp [heq]

theorem rational_X_mem (B : Subring (RatFunc ℚ))
    (v : ι → Valuation (RatFunc ℚ) ℤᵐ⁰)
    (hX : RatFunc.X ∈ B) (hv : ∀ i, v i RatFunc.X ≤ 1) :
    RatFunc.X ∈ intersection B v := (mem_intersection B v _).mpr ⟨hX, hv⟩

/-- The fraction-field structure uses the canonical subring inclusion. -/
theorem rational_isFractionRing (B : Subring (RatFunc ℚ))
    (v : ι → Valuation (RatFunc ℚ) ℤᵐ⁰)
    (hX : RatFunc.X ∈ B) (hv : ∀ i, v i RatFunc.X ≤ 1) :
    IsFractionRing (intersection B v) (RatFunc ℚ) :=
  RationalFunctionSubring.isFractionRing_of_X_mem _ (rational_X_mem B v hX hv)

end UnconditionalCounterexample.IntersectionDomain
