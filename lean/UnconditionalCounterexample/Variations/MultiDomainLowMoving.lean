import UnconditionalCounterexample.Variations.MultiDomainCube
import UnconditionalCounterexample.AtomProfiles

/-!
# The moving order-one divisors in the multivariate construction

The successive corrections to the first coordinate are actual units in the
horizontal localization. Their displayed primary and guard values determine
all vertical values of the resulting sequence.
-/

noncomputable section
namespace UnconditionalCounterexample.Variations.MultiDomain

open WithZero PrimaryWordProfiles

variable {r : ℕ} {A : Data (r+1)}

/-- The q-columns complementing the singleton columns of the cube chain. -/
structure MovingData (A : Data (r+1)) extends CubeData A where
  qRatio : ℕ → (poleAlgebra A)ˣ
  q_primary : ∀ n j, A.primary j ((qRatio n : poleAlgebra A) : FunctionField (r+1)) =
    exp (-qWeight n j)
  q_guard : ∀ n p, A.guard p ((qRatio n : poleAlgebra A) : FunctionField (r+1)) = 1
  t_exact : ∀ j, A.primary j (coordinate 0) = exp (-primaryAtomProfile 0 j)

namespace MovingData
variable (M : MovingData A)

def multiplier : ℕ → (poleAlgebra A)ˣ
  | 0 => 1
  | n+1 => multiplier n * M.b (n+1) / M.qRatio n

def movingPole (n : ℕ) : poleAlgebra A :=
  algebraMap (Polys (r+1)) (poleAlgebra A) (MvPolynomial.X 0) * M.multiplier n

@[simp] theorem movingPole_zero : (M.movingPole 0 : FunctionField (r+1)) = coordinate 0 := by
  simp [movingPole, multiplier, coordinate]

theorem movingPole_succ (n : ℕ) :
    (M.movingPole (n+1) : FunctionField (r+1)) =
      (M.movingPole n : FunctionField (r+1)) * (M.b (n+1) : poleAlgebra A) /
        (M.qRatio n : poleAlgebra A) := by
  have hi : (((((M.qRatio n)⁻¹ : (poleAlgebra A)ˣ) : poleAlgebra A) : FunctionField (r+1))) =
      (((M.qRatio n : poleAlgebra A) : FunctionField (r+1)))⁻¹ :=
    eq_inv_of_mul_eq_one_left (congrArg (poleAlgebra A).subtype (M.qRatio n).inv_mul)
  simp [movingPole, multiplier, div_eq_mul_inv, hi, mul_assoc]

theorem primary_moving (n j : ℕ) :
    A.primary j (M.movingPole n : FunctionField (r+1)) = exp (-primaryAtomProfile n j) := by
  induction n with
  | zero => simpa using M.t_exact j
  | succ n ih =>
    rw [M.movingPole_succ, map_div₀, map_mul, ih, M.b_primary, M.q_primary,
      ← exp_add, ← exp_sub, AtomProfiles.primary_recurrence]
    congr 1
    ring

theorem guard_moving (n : ℕ) (p : GuardSupport.PrimeIndex) :
    A.guard p (M.movingPole n : FunctionField (r+1)) = 1 := by
  induction n with
  | zero => simpa using M.t_guard p
  | succ n ih => rw [M.movingPole_succ, map_div₀, map_mul, ih, M.b_guard, M.q_guard, mul_one, div_one]

/-- Every horizontal valuation integral on the pole algebra sees precisely
the value of the first coordinate at every moving term. -/
theorem horizontal_moving (v : Valuation (FunctionField (r+1)) ℤᵐ⁰)
    (hv : ∀ x ∈ poleAlgebra A, v x ≤ 1) (n : ℕ) :
    v (M.movingPole n : FunctionField (r+1)) = v (coordinate 0) := by
  have hu := DiscreteOrders.order_eq_zero_of_isUnit (poleAlgebra A).toSubring v hv
    (M.multiplier n).isUnit
  have hn : ((M.multiplier n : poleAlgebra A) : FunctionField (r+1)) ≠ 0 :=
    fun h ↦ (M.multiplier n).ne_zero (Subtype.ext h)
  change v (coordinate 0 * ((M.multiplier n : poleAlgebra A) : FunctionField (r+1))) = _
  rw [map_mul, (DiscreteOrders.order_eq_zero_iff v hn).mp hu, mul_one]

def movingElement (n : ℕ) : ordinary A :=
  ⟨M.movingPole n, (mem_ordinary A).mpr ⟨(M.movingPole n).property, fun j ↦
    (M.primary_moving n j).trans_le (exp_le_one_iff.mpr (neg_nonpos.mpr (primaryAtomProfile_nonneg n j))),
    fun p ↦ (M.guard_moving n p).le⟩⟩

theorem movingElement_ne_zero (n : ℕ) : M.movingElement n ≠ 0 := by
  intro h
  have h₀ : (M.movingPole n : FunctionField (r+1)) = 0 := congrArg (ordinary A).subtype h
  exact exp_ne_zero (a := -primaryAtomProfile n 0) (by rw [← M.primary_moving, h₀, map_zero])

variable (c : Fin (r+1) → ℚ) (hc : MultivariateFibres.Retained (denominators A) c)
  (q : ℕ) [Fact q.Prime]

private abbrev poleEval := MultivariateFibres.pointEval (denominators A) (poleAlgebra A) c hc

/-- The correct local unit condition at the optional evaluation is preserved
by the whole recurrence, even though its q-ratios need not divide in the
ordinary domain. -/
theorem moving_point_unit (hc₀ : c 0 = 1)
    (hb : ∀ n, ∃ u : (PointPullback.localRationals q)ˣ,
      ((u : PointPullback.localRationals q) : ℚ) = poleEval c hc (M.b n : poleAlgebra A))
    (hq : ∀ n, ∃ u : (PointPullback.localRationals q)ˣ,
      ((u : PointPullback.localRationals q) : ℚ) = poleEval c hc (M.qRatio n : poleAlgebra A))
    (n : ℕ) : ∃ u : (PointPullback.localRationals q)ˣ,
      ((u : PointPullback.localRationals q) : ℚ) = point A c hc (M.movingElement n) := by
  let W := PointPullback.localRationals q
  let ev := poleEval c hc
  have h (n : ℕ) : ∃ u : Wˣ, ((u : W) : ℚ) = ev (M.multiplier n : poleAlgebra A) := by
    induction n with
    | zero => exact ⟨1, by simp [multiplier]⟩
    | succ n ih =>
      obtain ⟨u, hu⟩ := ih
      obtain ⟨b, hbu⟩ := hb (n+1)
      obtain ⟨v, hqu⟩ := hq n
      have hi : ev (((M.qRatio n)⁻¹ : (poleAlgebra A)ˣ) : poleAlgebra A) =
          ((((v⁻¹ : Wˣ) : W) : ℚ)) := by
        apply (mul_left_injective₀ (show ((v : W) : ℚ) ≠ 0 from fun he ↦ v.ne_zero (Subtype.ext he)))
        change ev _ * ((v : W) : ℚ) = ((((v⁻¹ : Wˣ) : W) : ℚ) * ((v : W) : ℚ))
        rw [← Subring.coe_mul, v.inv_mul, Subring.coe_one, hqu, ← map_mul, (M.qRatio n).inv_mul, map_one]
      refine ⟨u * b / v, ?_⟩
      simp only [div_eq_mul_inv, Units.val_mul, Subring.coe_mul, multiplier, map_mul, hu, hbu, hi]
      rfl
  obtain ⟨u, hu⟩ := h n
  refine ⟨u, ?_⟩
  change ((u : W) : ℚ) = ev (M.movingPole n)
  simpa [movingPole, ev, poleEval, hc₀] using hu

end MovingData
end UnconditionalCounterexample.Variations.MultiDomain
