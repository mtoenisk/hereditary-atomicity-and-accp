import UnconditionalCounterexample.Variations.MultiDomain
import UnconditionalCounterexample.PaperCubeChain

/-!
# The multivariate cube chain

The disjoint primary columns of the normalized singleton ratios control the
powers of the first coordinate that remain after removing any finite prefix.
At the rational point each extra division is by a local unit, so the same
literal fractions give a strict chain in the pullback.
-/

noncomputable section
namespace UnconditionalCounterexample.Variations.MultiDomain

open WithZero NormalizedWords PrimaryWordProfiles IntersectionDomain

variable {r : ℕ} {A : Data (r+1)}

/-- The first coordinate and the even singleton columns for its cube chain. -/
structure CubeData (A : Data (r+1)) where
  b : ℕ → (poleAlgebra A)ˣ
  b_primary : ∀ n j, A.primary j ((b n : poleAlgebra A) : FunctionField (r+1)) = exp (-bWeight n j)
  b_guard : ∀ n p, A.guard p ((b n : poleAlgebra A) : FunctionField (r+1)) = 1
  t_primary : ∀ j, A.primary j (coordinate 0) ≤ exp (-1)
  t_guard : ∀ p, A.guard p (coordinate 0) = 1

namespace CubeData

variable (C : CubeData A)

def parameter : ordinary A := ⟨coordinate 0, (mem_ordinary A).mpr
  ⟨(poleAlgebra A).algebraMap_mem _, fun j ↦ (C.t_primary j).trans (exp_le_one_iff.mpr (by decide)),
    fun p ↦ (C.t_guard p).le⟩⟩

theorem parameter_ne_zero : C.parameter ≠ 0 := by
  intro h
  apply MvPolynomial.X_ne_zero (R := ℚ) (0 : Fin (r+1))
  apply IsFractionRing.injective (Polys (r+1)) (FunctionField (r+1))
  simpa [parameter, coordinate] using congrArg (ordinary A).subtype h

def ratio (n : ℕ) : ordinary A :=
  ⟨(C.b n : poleAlgebra A), (mem_ordinary A).mpr ⟨(C.b n : poleAlgebra A).property, fun j ↦
    (C.b_primary n j) ▸ exp_le_one_iff.mpr (neg_nonpos.mpr (PaperCubeChain.bWeight_nonneg _ _)),
    fun p ↦ (C.b_guard n p).le⟩⟩

theorem ratio_not_isUnit (n : ℕ) : ¬ IsUnit (C.ratio n) := by
  intro hu
  obtain ⟨y, hy⟩ := isUnit_iff_exists_inv.mp hu
  let V := A.primary (2*n)
  have hb : V (C.ratio n : FunctionField (r+1)) < 1 := by
    change A.primary (2*n) ((C.b n : poleAlgebra A) : FunctionField (r+1)) < 1
    rw [C.b_primary, exp_lt_one_iff]
    simp [bWeight]
  have hy' : V (y : FunctionField (r+1)) ≤ 1 := ((mem_ordinary A).mp y.property).2.1 _
  have hlt : V ((C.ratio n : FunctionField (r+1)) * y) < 1 := by
    rw [map_mul]
    calc
      _ ≤ V (C.ratio n : FunctionField (r+1)) * 1 := mul_le_mul_of_nonneg_left hy' zero_le
      _ < 1 := by simpa using hb
  rw [show (C.ratio n : FunctionField (r+1)) * y = 1 from congrArg (ordinary A).subtype hy,
    map_one] at hlt
  exact (lt_irrefl _) hlt

def prefixUnit (n : ℕ) : (poleAlgebra A)ˣ := ∏ j ∈ Finset.range n, C.b j

theorem prefix_ne_zero (n : ℕ) : ((C.prefixUnit n : poleAlgebra A) : FunctionField (r+1)) ≠ 0 :=
  fun h ↦ (C.prefixUnit n).ne_zero (Subtype.ext h)

def chainValue (n : ℕ) : FunctionField (r+1) :=
  coordinate 0 ^ 3 / ((C.prefixUnit n : poleAlgebra A) : FunctionField (r+1))

theorem chainValue_mem (n : ℕ) : C.chainValue n ∈ ordinary A := by
  apply (div_mem_iff _ _ (C.prefix_ne_zero n)).mpr
  constructor
  · let u := C.prefixUnit n
    have hi : ((((u⁻¹ : (poleAlgebra A)ˣ) : poleAlgebra A) : FunctionField (r+1))) =
        ((u : poleAlgebra A) : FunctionField (r+1))⁻¹ :=
      eq_inv_of_mul_eq_one_left (congrArg (poleAlgebra A).subtype u.inv_mul)
    rw [div_eq_mul_inv, ← hi]
    exact (poleAlgebra A).mul_mem ((poleAlgebra A).pow_mem ((poleAlgebra A).algebraMap_mem _) _)
      ((u⁻¹ : (poleAlgebra A)ˣ) : poleAlgebra A).property
  · have hcoe : ((C.prefixUnit n : poleAlgebra A) : FunctionField (r+1)) =
        ∏ j ∈ Finset.range n, ((C.b j : poleAlgebra A) : FunctionField (r+1)) := by simp [prefixUnit]
    rw [hcoe]
    rintro (i | p)
    · change A.primary i (coordinate 0 ^ 3) ≤ A.primary i _
      simp only [map_prod, C.b_primary, map_pow]
      rw [prod_exp_neg]
      calc
        _ ≤ exp (-1 : ℤ)^3 := pow_le_pow_left₀ zero_le (C.t_primary i) _
        _ = exp (-3 : ℤ) := by norm_num [← exp_nsmul, nsmul_eq_mul]
        _ ≤ _ := exp_le_exp.mpr (neg_le_neg (PaperCubeChain.sum_bWeight_le_three _ _))
    · change A.guard p (coordinate 0 ^ 3) ≤ A.guard p _
      simp [map_prod, C.b_guard, C.t_guard]

def endpoint (n : ℕ) : ordinary A := ⟨C.chainValue n, C.chainValue_mem n⟩

@[simp] theorem endpoint_zero : C.endpoint 0 = C.parameter^3 := by
  apply Subtype.ext
  simp [endpoint, chainValue, prefixUnit, parameter]

theorem endpoint_ne_zero (n : ℕ) : C.endpoint n ≠ 0 := by
  intro h
  have ht : (coordinate 0 : FunctionField (r+1)) ≠ 0 := fun he ↦ C.parameter_ne_zero (Subtype.ext he)
  exact div_ne_zero (pow_ne_zero 3 ht) (C.prefix_ne_zero n) (congrArg (ordinary A).subtype h)

theorem endpoint_recurrence (n : ℕ) : C.endpoint n = C.endpoint (n+1) * C.ratio n := by
  apply Subtype.ext
  change C.chainValue n = C.chainValue (n+1) * ((C.b n : poleAlgebra A) : FunctionField (r+1))
  simp only [chainValue, prefixUnit, Finset.prod_range_succ, Units.val_mul, Subalgebra.coe_mul]
  rw [div_mul_eq_div_div, div_mul_cancel₀ _ (fun h ↦ (C.b n).ne_zero (Subtype.ext h))]

theorem ordinary_chain : HasStrictChainAt (C.parameter^3) :=
  ⟨C.endpoint, C.endpoint_zero, C.endpoint_ne_zero,
    strictMono_principalIdeals_of_nonunit_recurrence _ _ C.endpoint_ne_zero C.ratio_not_isUnit
      C.endpoint_recurrence⟩

variable (c : Fin (r+1) → ℚ) (hc : MultivariateFibres.Retained (denominators A) c)

@[simp] theorem point_parameter : point A c hc C.parameter = c 0 := by
  change MultivariateFibres.pointEval _ _ c hc (algebraMap (Polys (r+1)) (poleAlgebra A)
    (MvPolynomial.X 0)) = c 0
  simp

private theorem pullback_le_ordinary (q : ℕ) [Fact q.Prime] : pullback A c hc q ≤ ordinary A := by
  rintro _ ⟨x, _, rfl⟩
  exact x.property

/-- At the reserved point the first coordinate is one and each singleton
ratio is a q-unit. Dividing out a prefix therefore preserves q-integrality. -/
theorem pullback_chain (hc₀ : c 0 = 1) (q : ℕ) [Fact q.Prime]
    (hu : ∀ n, ∃ u : (PointPullback.localRationals q)ˣ,
      ((u : PointPullback.localRationals q) : ℚ) = point A c hc (C.ratio n)) :
    ∃ t : pullback A c hc q, (t : FunctionField (r+1)) = coordinate 0 ∧ HasStrictChainAt (t^3) := by
  let W := PointPullback.localRationals q
  let ev := point A c hc
  let D := pullback A c hc q
  let lift (x : ordinary A) (hx : ev x ∈ W) : D := ⟨x, ⟨x, hx, rfl⟩⟩
  have ht : ev C.parameter ∈ W := by simp [ev, C.point_parameter c hc, hc₀]
  have hb (n : ℕ) : ev (C.ratio n) ∈ W := by
    obtain ⟨u, h⟩ := hu n
    exact h ▸ (u : W).property
  have he (n : ℕ) : ev (C.endpoint n) ∈ W := by
    induction n with
    | zero => simpa using W.pow_mem ht 3
    | succ n ih =>
      obtain ⟨u, hu⟩ := hu n
      have hr := congrArg ev (C.endpoint_recurrence n)
      rw [map_mul, ← hu] at hr
      have hi : ev (C.endpoint n) * (((u⁻¹ : Wˣ) : W) : ℚ) = ev (C.endpoint (n+1)) := by
        rw [hr, mul_assoc, ← Subring.coe_mul]
        simp
      exact hi ▸ W.mul_mem ih ((u⁻¹ : Wˣ) : W).property
  let x (n : ℕ) := lift (C.endpoint n) (he n)
  let b (n : ℕ) := lift (C.ratio n) (hb n)
  have hn (n : ℕ) : x n ≠ 0 := fun h ↦ C.endpoint_ne_zero n (Subtype.ext (congrArg D.subtype h))
  have hnu (n : ℕ) : ¬ IsUnit (b n) :=
    fun h ↦ C.ratio_not_isUnit n (h.map (Subring.inclusion (pullback_le_ordinary c hc q)))
  exact ⟨lift C.parameter ht, rfl, x, Subtype.ext (congrArg (ordinary A).subtype C.endpoint_zero), hn,
    strictMono_principalIdeals_of_nonunit_recurrence x b hn hnu fun n ↦
      Subtype.ext (congrArg (ordinary A).subtype (C.endpoint_recurrence n))⟩

end CubeData
end UnconditionalCounterexample.Variations.MultiDomain
