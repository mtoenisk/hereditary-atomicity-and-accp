import Mathlib.RingTheory.PowerBasis
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.LinearAlgebra.Basis.SMul
import HereditaryAtomicity.DVRBase.CompleteEstimates

/-!
# Bounds on coefficients in power windows

Consecutive powers form a basis with the stated termwise norm bound over a complete
nonarchimedean field. The extension may be inseparable and the residue field infinite.
-/

noncomputable section
namespace HereditaryAtomicity.DVRBase

open scoped BigOperators

variable {K L : Type*} [NormedField K] [Field L] [Algebra K L]

/-- The top reduction coefficients in a power basis are the negatives of the
nonleading minimal-polynomial coefficients. -/
theorem powerBasis_repr_top (b : PowerBasis K L) (i : Fin b.dim) :
    b.basis.repr (b.gen ^ b.dim) i = -(minpoly K b.gen).coeff i := by
  have h := congrArg (fun p : Polynomial K => p.coeff i) b.minpolyGen_eq
  simp only [PowerBasis.minpolyGen, Polynomial.coeff_sub,
    Polynomial.coeff_X_pow, Polynomial.finsetSum_coeff,
    Polynomial.coeff_C_mul, Polynomial.coeff_X_pow] at h
  have hi : (i : ℕ) ≠ b.dim := ne_of_lt i.isLt
  simpa [hi, Fin.val_inj, mul_ite] using congrArg Neg.neg h


/-- Evaluation of a polynomial shorter than the basis has its literal
coefficients as power-basis coordinates. -/
theorem powerBasis_repr_aeval (b : PowerBasis K L) (p : Polynomial K)
    (hp : p.natDegree < b.dim) (i : Fin b.dim) :
    b.basis.repr (Polynomial.aeval b.gen p) i = p.coeff i := by
  classical
  rw [Polynomial.aeval_eq_sum_range' hp, Finset.sum_range]
  have hrepr (j : Fin b.dim) :
      b.basis.repr (b.gen ^ (j : ℕ)) i = if j = i then 1 else 0 := by
    rw [← b.basis_eq_pow]
    exact b.basis.repr_self_apply j i
  simp only [map_sum, map_smul, Finset.sum_apply', Finsupp.smul_apply, smul_eq_mul]
  change (∑ j : Fin b.dim, p.coeff j * b.basis.repr (b.gen ^ (j : ℕ)) i) = _
  simp [hrepr, mul_ite]


/-- A column bound for multiplication propagates a coordinate bound, with no
factor depending on the dimension because the scalar norm is ultrametric. -/
theorem powerBasis_bound_mul [IsUltrametricDist K]
    (b : PowerBasis K L) (r : ℝ) (hr : 0 ≤ r)
    (t x : L) (C A : ℝ) (hC : 0 ≤ C)
    (hcols : ∀ i j : Fin b.dim,
      ‖b.basis.repr (t * b.basis j) i‖ * r ^ (i : ℕ) ≤ C * r ^ (j : ℕ))
    (hx : ∀ j : Fin b.dim, ‖b.basis.repr x j‖ * r ^ (j : ℕ) ≤ A)
    (i : Fin b.dim) :
    ‖b.basis.repr (t * x) i‖ * r ^ (i : ℕ) ≤ C * A := by
  classical
  let : Nonempty (Fin b.dim) := ⟨⟨0, b.dim_pos⟩⟩
  have heq : b.basis.repr (t * x) i =
      ∑ j : Fin b.dim, b.basis.repr x j * b.basis.repr (t * b.basis j) i := by
    nth_rw 1 [← b.basis.sum_repr x]
    simp [Finset.mul_sum, Algebra.mul_smul_comm, map_sum, map_smul,
      smul_eq_mul]
  rw [heq]
  obtain ⟨j, _, hj⟩ := IsUltrametricDist.exists_norm_finsetSum_le_of_nonempty
    (Finset.univ_nonempty : (Finset.univ : Finset (Fin b.dim)).Nonempty)
    (fun j : Fin b.dim => b.basis.repr x j * b.basis.repr (t * b.basis j) i)
  calc
    _ ≤ ‖b.basis.repr x j * b.basis.repr (t * b.basis j) i‖ * r ^ (i : ℕ) :=
      mul_le_mul_of_nonneg_right hj (pow_nonneg hr _)
    _ = ‖b.basis.repr x j‖ *
        (‖b.basis.repr (t * b.basis j) i‖ * r ^ (i : ℕ)) := by rw [norm_mul]; ring
    _ ≤ ‖b.basis.repr x j‖ * (C * r ^ (j : ℕ)) :=
      mul_le_mul_of_nonneg_left (hcols i j) (norm_nonneg _)
    _ = C * (‖b.basis.repr x j‖ * r ^ (j : ℕ)) := by ring
    _ ≤ C * A := mul_le_mul_of_nonneg_left (hx j) hC

/-- The coordinates of the inverse of the generator follow by evaluating the
minimal polynomial divided by X. -/
theorem powerBasis_repr_inv (b : PowerBasis K L) (hy : b.gen ≠ 0)
    (i : Fin b.dim) :
    b.basis.repr b.gen⁻¹ i =
      -((minpoly K b.gen).coeff 0)⁻¹ * (minpoly K b.gen).coeff ((i : ℕ) + 1) := by
  let p := minpoly K b.gen
  have hp0 : p.coeff 0 ≠ 0 := minpoly.coeff_zero_ne_zero b.isIntegral_gen hy
  have heq := congrArg (Polynomial.aeval b.gen) (Polynomial.divX_mul_X_add p)
  simp only [map_add, map_mul, Polynomial.aeval_X, Polynomial.aeval_C,
    show Polynomial.aeval b.gen p = 0 from minpoly.aeval K b.gen] at heq
  have hinv : b.gen⁻¹ = -(p.coeff 0)⁻¹ • Polynomial.aeval b.gen p.divX := by
    apply mul_left_cancel₀ hy
    rw [mul_inv_cancel₀ hy, Algebra.mul_smul_comm]
    have hh : b.gen * Polynomial.aeval b.gen p.divX =
        -algebraMap K L (p.coeff 0) := by
      rw [mul_comm]
      exact eq_neg_of_add_eq_zero_left heq
    rw [hh, Algebra.smul_def]
    simp [hp0]
  rw [hinv, map_smul, Finsupp.smul_apply, smul_eq_mul,
    powerBasis_repr_aeval b p.divX]
  · simp [p, Polynomial.coeff_divX]
  · rw [Polynomial.natDegree_divX_eq_natDegree_tsub_one, b.natDegree_minpoly]
    exact Nat.sub_lt b.dim_pos (by decide)

/-- The minimal-polynomial coefficient estimates bound each column of
multiplication by the generator. -/
theorem powerBasis_gen_column_bound (b : PowerBasis K L) (r : ℝ) (hr : 0 ≤ r)
    (hcoeff : ∀ n, ‖(minpoly K b.gen).coeff n‖ * r ^ n ≤ r ^ b.dim)
    (i j : Fin b.dim) :
    ‖b.basis.repr (b.gen * b.basis j) i‖ * r ^ (i : ℕ) ≤ r * r ^ (j : ℕ) := by
  rw [b.basis_eq_pow, ← pow_succ']
  by_cases hj : (j : ℕ) + 1 = b.dim
  · rw [hj, powerBasis_repr_top, norm_neg]
    simpa [← hj, pow_succ, mul_comm] using hcoeff i
  · have hjlt : (j : ℕ) + 1 < b.dim := lt_of_le_of_ne (Nat.succ_le_of_lt j.isLt) hj
    let k : Fin b.dim := ⟨(j : ℕ) + 1, hjlt⟩
    change ‖b.basis.repr (b.gen ^ (k : ℕ)) i‖ * r ^ (i : ℕ) ≤ _
    rw [← b.basis_eq_pow, b.basis.repr_self_apply]
    split_ifs with hki
    · subst i
      simp [k, pow_succ, mul_comm]
    · simpa using mul_nonneg hr (pow_nonneg hr (j : ℕ))

/-- The coefficient estimates and exact constant term control the inverse
of the generator in the original power basis. -/
theorem powerBasis_inv_bound (b : PowerBasis K L) (hy : b.gen ≠ 0)
    (r : ℝ) (hr : 0 < r)
    (hcoeff : ∀ n, ‖(minpoly K b.gen).coeff n‖ * r ^ n ≤ r ^ b.dim)
    (hconst : ‖(minpoly K b.gen).coeff 0‖ = r ^ b.dim) (i : Fin b.dim) :
    ‖b.basis.repr b.gen⁻¹ i‖ * r ^ (i : ℕ) ≤ r⁻¹ := by
  rw [powerBasis_repr_inv b hy, norm_mul, norm_neg, norm_inv, hconst]
  calc
    _ = (‖(minpoly K b.gen).coeff ((i : ℕ) + 1)‖ * r ^ (i : ℕ)) / r ^ b.dim := by ring
    _ ≤ 1 / r := (div_le_div_iff₀ (pow_pos hr _) hr).mpr (by
      simpa [pow_succ, mul_assoc] using hcoeff ((i : ℕ) + 1))
    _ = r⁻¹ := one_div r

/-- Each column of multiplication by the inverse has the reciprocal bound. -/
theorem powerBasis_inv_column_bound (b : PowerBasis K L) (hy : b.gen ≠ 0)
    (r : ℝ) (hr : 0 < r)
    (hcoeff : ∀ n, ‖(minpoly K b.gen).coeff n‖ * r ^ n ≤ r ^ b.dim)
    (hconst : ‖(minpoly K b.gen).coeff 0‖ = r ^ b.dim)
    (i j : Fin b.dim) :
    ‖b.basis.repr (b.gen⁻¹ * b.basis j) i‖ * r ^ (i : ℕ) ≤ r⁻¹ * r ^ (j : ℕ) := by
  rw [b.basis_eq_pow]
  by_cases hj : (j : ℕ) = 0
  · simpa [hj] using powerBasis_inv_bound b hy r hr hcoeff hconst i
  · have hjpos : 0 < (j : ℕ) := Nat.pos_of_ne_zero hj
    let k : Fin b.dim := ⟨(j : ℕ) - 1, lt_of_le_of_lt (Nat.sub_le _ _) j.isLt⟩
    have hj' : (j : ℕ) = (k : ℕ) + 1 := by dsimp [k]; omega
    rw [hj', pow_succ', inv_mul_cancel_left₀ hy, ← b.basis_eq_pow,
      b.basis.repr_self_apply]
    have hr' : r⁻¹ * r ^ ((k : ℕ) + 1) = r ^ (k : ℕ) := by
      rw [pow_succ', inv_mul_cancel_left₀ hr.ne']
    rw [hr']
    split_ifs with hki
    · subst i
      simp
    · simpa using pow_nonneg hr.le (k : ℕ)

/-- Every integer power has a lossless expansion in the unshifted power basis.
The only analytic inputs are the coefficient inequalities and the exact norm
of the minimal polynomial's constant term. -/
theorem powerBasis_zpow_bound [IsUltrametricDist K]
    (b : PowerBasis K L) (hy : b.gen ≠ 0) (r : ℝ) (hr : 0 < r)
    (hcoeff : ∀ n, ‖(minpoly K b.gen).coeff n‖ * r ^ n ≤ r ^ b.dim)
    (hconst : ‖(minpoly K b.gen).coeff 0‖ = r ^ b.dim)
    (a : ℤ) (i : Fin b.dim) :
    ‖b.basis.repr (b.gen ^ a) i‖ * r ^ (i : ℕ) ≤ r ^ a := by
  have hzero : ∀ i : Fin b.dim,
      ‖b.basis.repr (b.gen ^ (0 : ℤ)) i‖ * r ^ (i : ℕ) ≤ r ^ (0 : ℤ) := by
    intro i
    let z : Fin b.dim := ⟨0, b.dim_pos⟩
    have heq : b.gen ^ (0 : ℤ) = b.basis z := by simp [b.basis_eq_pow, z]
    rw [heq, b.basis.repr_self_apply]
    split_ifs with hzi
    · subst i
      simp [z]
    · simp
  have hsucc (a : ℤ)
      (h : ∀ i : Fin b.dim, ‖b.basis.repr (b.gen ^ a) i‖ * r ^ (i : ℕ) ≤ r ^ a) :
      ∀ i : Fin b.dim, ‖b.basis.repr (b.gen ^ (a + 1)) i‖ * r ^ (i : ℕ) ≤ r ^ (a + 1) := by
    intro i
    simpa [zpow_add₀ hy, zpow_add₀ hr.ne', mul_comm] using
      powerBasis_bound_mul b r hr.le b.gen (b.gen ^ a) r (r ^ a) hr.le
        (powerBasis_gen_column_bound b r hr.le hcoeff) h i
  have hpred (a : ℤ)
      (h : ∀ i : Fin b.dim, ‖b.basis.repr (b.gen ^ a) i‖ * r ^ (i : ℕ) ≤ r ^ a) :
      ∀ i : Fin b.dim, ‖b.basis.repr (b.gen ^ (a - 1)) i‖ * r ^ (i : ℕ) ≤ r ^ (a - 1) := by
    intro i
    simpa [zpow_sub₀ hy, zpow_sub₀ hr.ne', div_eq_mul_inv, mul_comm] using
      powerBasis_bound_mul b r hr.le b.gen⁻¹ (b.gen ^ a) r⁻¹ (r ^ a) (inv_nonneg.mpr hr.le)
        (powerBasis_inv_column_bound b hy r hr hcoeff hconst) h i
  exact Int.induction_on a hzero (fun n h => hsucc n h) (fun n h => hpred (-n) h) i

/-- The consecutive window starting at w, obtained by multiplying the original
power basis by the nonzero element gen^w. -/
def powerWindowBasis (b : PowerBasis K L) (hy : b.gen ≠ 0) (w : ℤ) :
    Module.Basis (Fin b.dim) K L :=
  (Units.mk0 (b.gen ^ w) (zpow_ne_zero w hy)) • b.basis

@[simp] theorem powerWindowBasis_apply (b : PowerBasis K L) (hy : b.gen ≠ 0)
    (w : ℤ) (i : Fin b.dim) :
    powerWindowBasis b hy w i = b.gen ^ (w + (i : ℤ)) := by
  simp [powerWindowBasis, Units.smul_def, b.basis_eq_pow, zpow_add₀ hy]

/-- Shifting the power window translates the exponent before taking the
original coordinates. -/
theorem powerWindowBasis_repr_zpow (b : PowerBasis K L) (hy : b.gen ≠ 0)
    (w a : ℤ) (i : Fin b.dim) :
    (powerWindowBasis b hy w).repr (b.gen ^ a) i = b.basis.repr (b.gen ^ (a - w)) i := by
  change b.basis.repr ((b.gen ^ w)⁻¹ * b.gen ^ a) i = _
  rw [mul_comm, ← div_eq_mul_inv, ← zpow_sub₀ hy]

/-- Lossless coefficient bounds in every consecutive integer window, with
explicit minimal-polynomial estimates as inputs. -/
theorem powerWindowBasis_zpow_bound [IsUltrametricDist K]
    (b : PowerBasis K L) (hy : b.gen ≠ 0) (r : ℝ) (hr : 0 < r)
    (hcoeff : ∀ n, ‖(minpoly K b.gen).coeff n‖ * r ^ n ≤ r ^ b.dim)
    (hconst : ‖(minpoly K b.gen).coeff 0‖ = r ^ b.dim)
    (w a : ℤ) (i : Fin b.dim) :
    ‖(powerWindowBasis b hy w).repr (b.gen ^ a) i‖ * r ^ (w + (i : ℤ)) ≤ r ^ a := by
  rw [powerWindowBasis_repr_zpow, zpow_add₀ hr.ne', zpow_natCast]
  calc
    _ = (‖b.basis.repr (b.gen ^ (a - w)) i‖ * r ^ (i : ℕ)) * r ^ w := by ring
    _ ≤ r ^ (a - w) * r ^ w := mul_le_mul_of_nonneg_right
      (powerBasis_zpow_bound b hy r hr hcoeff hconst (a - w) i) (zpow_nonneg hr.le _)
    _ = r ^ a := by rw [← zpow_add₀ hr.ne']; simp

section CompleteField

variable {F E : Type*} [NontriviallyNormedField F] [CompleteSpace F]
  [IsUltrametricDist F] [NormedField E] [NormedAlgebra F E]
  [Algebra.IsAlgebraic F E]

/-- Every integer power expands without norm loss in a consecutive power basis over a
complete nonarchimedean field. -/
theorem norm_powerWindowBasis_zpow_term_le (b : PowerBasis F E) (hy : b.gen ≠ 0)
    (w a : ℤ) (i : Fin b.dim) :
    ‖(powerWindowBasis b hy w).repr (b.gen ^ a) i • powerWindowBasis b hy w i‖ ≤
      ‖b.gen ^ a‖ := by
  rw [norm_smul, powerWindowBasis_apply, norm_zpow, norm_zpow]
  apply powerWindowBasis_zpow_bound b hy ‖b.gen‖ (norm_pos_iff.mpr hy)
  · intro n
    simpa only [b.natDegree_minpoly] using norm_minpoly_coeff_mul_pow_le (K := F) b.gen n
  · simpa only [b.natDegree_minpoly] using norm_minpoly_coeff_zero (K := F) b.gen

/-- The lossless bound is unchanged after multiplying the power by a scalar
from the complete coefficient field. -/
theorem norm_powerWindowBasis_monomial_term_le (b : PowerBasis F E) (hy : b.gen ≠ 0)
    (c : F) (w a : ℤ) (i : Fin b.dim) :
    ‖(powerWindowBasis b hy w).repr (c • b.gen ^ a) i • powerWindowBasis b hy w i‖ ≤
      ‖c • b.gen ^ a‖ := by
  rw [map_smul, Finsupp.smul_apply, smul_eq_mul, mul_smul]
  simpa only [norm_smul] using mul_le_mul_of_nonneg_left (norm_powerWindowBasis_zpow_term_le b hy w a i)
    (norm_nonneg c)

/-- The additive order form omits exactly the zero coordinates, where the
source valuation is infinite. -/
theorem order_powerWindowBasis_monomial_term_ge (b : PowerBasis F E) (hy : b.gen ≠ 0)
    (c : F) (w a : ℤ) (i : Fin b.dim)
    (hi : (powerWindowBasis b hy w).repr (c • b.gen ^ a) i ≠ 0) :
    -Real.log ‖c • b.gen ^ a‖ ≤
      -Real.log ‖(powerWindowBasis b hy w).repr (c • b.gen ^ a) i •
        powerWindowBasis b hy w i‖ := by
  apply neg_le_neg
  exact Real.log_le_log (norm_pos_iff.mpr (smul_ne_zero hi
    ((powerWindowBasis b hy w).ne_zero i)))
    (norm_powerWindowBasis_monomial_term_le b hy c w a i)

end CompleteField

end HereditaryAtomicity.DVRBase
