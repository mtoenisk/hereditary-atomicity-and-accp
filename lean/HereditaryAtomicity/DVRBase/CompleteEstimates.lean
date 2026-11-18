import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Coefficient and coordinate estimates over a complete valued field

The spectral norm bounds the coordinates over a complete scalar field, including
inseparable extensions and infinite residue fields.
-/

noncomputable section
namespace HereditaryAtomicity.DVRBase

section Coefficients

variable {K L : Type*} [NontriviallyNormedField K] [CompleteSpace K]
  [IsUltrametricDist K] [NormedField L] [NormedAlgebra K L]
  [Algebra.IsAlgebraic K L]

/-- Each coefficient of a minimal polynomial is bounded by the corresponding
power of the norm of its root. This includes inseparable minimal polynomials. -/
theorem norm_minpoly_coeff_le_pow (x : L) {n : ℕ}
    (hn : n ≤ (minpoly K x).natDegree) :
    ‖(minpoly K x).coeff n‖ ≤ ‖x‖ ^ ((minpoly K x).natDegree - n) := by
  rcases hn.eq_or_lt with h | h
  · rw [h, (minpoly.monic (Algebra.IsIntegral.isIntegral x)).coeff_natDegree]
    simp
  · have hb : spectralValueTerms (minpoly K x) n ≤ spectralNorm K L x :=
      le_ciSup (spectralValueTerms_bddAbove (minpoly K x)) n
    rw [← NormedAlgebra.norm_eq_spectralNorm K x,
      spectralValueTerms_of_lt_natDegree _ h, one_div] at hb
    have hd : 0 < ((minpoly K x).natDegree : ℝ) - n :=
      sub_pos.mpr (by exact_mod_cast h)
    have hb' := (Real.rpow_inv_le_iff_of_pos (norm_nonneg _) (norm_nonneg _) hd).mp hb
    rwa [← Nat.cast_sub hn, Real.rpow_natCast] at hb'

/-- Multiplying by the matching root power gives the weighted coefficient
bound used in the companion-matrix recurrences. -/
theorem norm_minpoly_coeff_mul_pow_le (x : L) (n : ℕ) :
    ‖(minpoly K x).coeff n‖ * ‖x‖ ^ n ≤ ‖x‖ ^ (minpoly K x).natDegree := by
  by_cases hn : n ≤ (minpoly K x).natDegree
  · calc
      ‖(minpoly K x).coeff n‖ * ‖x‖ ^ n ≤
          ‖x‖ ^ ((minpoly K x).natDegree - n) * ‖x‖ ^ n :=
        mul_le_mul_of_nonneg_right (norm_minpoly_coeff_le_pow x hn) (by positivity)
      _ = ‖x‖ ^ (minpoly K x).natDegree := by
        rw [← pow_add, Nat.sub_add_cancel hn]
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (Nat.lt_of_not_ge hn), norm_zero, zero_mul]
    positivity

/-- The constant coefficient has exactly the norm of the degree-th power of
the root, rather than merely an upper bound. -/
theorem norm_minpoly_coeff_zero (x : L) :
    ‖(minpoly K x).coeff 0‖ = ‖x‖ ^ (minpoly K x).natDegree := by
  have h := spectralNorm.spectralNorm_eq_norm_coeff_zero_rpow K L x
  rw [← NormedAlgebra.norm_eq_spectralNorm K x, one_div,
    Real.eq_rpow_inv (norm_nonneg _) (norm_nonneg _)] at h
  · simpa only [Real.rpow_natCast] using h.symm
  · exact_mod_cast (minpoly.natDegree_pos (Algebra.IsIntegral.isIntegral x)).ne'

end Coefficients

section Coordinates

variable {ι K E : Type*} [Fintype ι] [NontriviallyNormedField K]
  [CompleteSpace K] [NormedAddCommGroup E] [NormedSpace K E]

/-- One positive constant bounds every individual term of a finite basis
expansion by the norm of the element being expanded. -/
theorem exists_basis_term_norm_bound (b : Module.Basis ι K E) :
    ∃ C : ℝ, 0 < C ∧ ∀ (x : E) (i : ι), ‖b.repr x i • b i‖ ≤ C * ‖x‖ := by
  classical
  let : FiniteDimensional K E := Module.Finite.of_basis b
  let f : ι → E →L[K] K := fun i => (b.coord i).toContinuousLinearMap
  let C : ℝ := 1 + ∑ i, ‖f i‖ * ‖b i‖
  have hsum : 0 ≤ ∑ i, ‖f i‖ * ‖b i‖ :=
    Finset.sum_nonneg fun _ _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)
  refine ⟨C, by dsimp [C]; linarith, ?_⟩
  intro x i
  have hi : ‖f i‖ * ‖b i‖ ≤ C := by
    have := Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) =>
      mul_nonneg (norm_nonneg (f j)) (norm_nonneg (b j))) (Finset.mem_univ i)
    dsimp [C]
    linarith
  have hcoord : ‖b.repr x i‖ ≤ ‖f i‖ * ‖x‖ := (f i).le_opNorm x
  calc
    ‖b.repr x i • b i‖ = ‖b.repr x i‖ * ‖b i‖ := norm_smul _ _
    _ ≤ (‖f i‖ * ‖x‖) * ‖b i‖ := mul_le_mul_of_nonneg_right hcoord (norm_nonneg _)
    _ = (‖f i‖ * ‖b i‖) * ‖x‖ := by ring
    _ ≤ C * ‖x‖ := mul_le_mul_of_nonneg_right hi (norm_nonneg _)

/-- The logarithmic form of the basis-term bound. Zero coordinates are omitted,
as additive real order is finite only on nonzero elements. -/
theorem exists_basis_term_order_bound (b : Module.Basis ι K E) :
    ∃ Ω : ℝ, 0 ≤ Ω ∧ ∀ (x : E), x ≠ 0 → ∀ (i : ι), b.repr x i ≠ 0 →
      -Real.log ‖x‖ - Ω ≤ -Real.log ‖b.repr x i • b i‖ := by
  obtain ⟨C, hC, hb⟩ := exists_basis_term_norm_bound b
  let C' : ℝ := max 1 C
  have hC' : 0 < C' := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  refine ⟨Real.log C', Real.log_nonneg (le_max_left _ _), ?_⟩
  intro x hx i hi
  have hterm : 0 < ‖b.repr x i • b i‖ :=
    norm_pos_iff.mpr (smul_ne_zero hi (b.ne_zero i))
  have hxnorm : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hle : ‖b.repr x i • b i‖ ≤ C' * ‖x‖ :=
    (hb x i).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hxnorm.le)
  have hlog := Real.log_le_log hterm hle
  rw [Real.log_mul hC'.ne' hxnorm.ne'] at hlog
  linarith

end Coordinates

end HereditaryAtomicity.DVRBase
