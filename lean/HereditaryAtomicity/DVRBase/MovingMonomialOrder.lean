import HereditaryAtomicity.DVRBase.MovingTower

noncomputable section
namespace HereditaryAtomicity.DVRBase
open scoped BigOperators

variable (K : Type*) {E : Type*} [NormedField K] [NormedField E] [NormedAlgebra K E]

/-- The actual finite-field monomial has the literal product norm. -/
theorem norm_movingMonomial_eq_prod (y : ℕ → Eˣ) (n : ℕ) (α : Fin n → ℤ) :
    ‖movingMonomial K y n α‖ = ∏ i : Fin n, ‖(y i.val : E)‖ ^ α i := by
  change ‖(movingMonomial K y n α : E)‖ = _
  rw [movingMonomial_coe]
  change ‖(Units.coeHom E) (∏ i : Fin n, y i.val ^ α i)‖ = _
  rw [map_prod, norm_prod]
  simp only [Units.coeHom_apply, Units.val_zpow_eq_zpow_val, norm_zpow]

/-- Additive order of a genuine moving monomial, with arbitrary integer exponents. -/
theorem order_movingMonomial_eq_sum (y : ℕ → Eˣ) (n : ℕ) (α : Fin n → ℤ)
    (c : K) (hc : c ≠ 0) :
    -Real.log ‖c • movingMonomial K y n α‖ =
      -Real.log ‖c‖ + ∑ i : Fin n, (α i : ℝ) * (-Real.log ‖(y i.val : E)‖) := by
  rw [norm_smul, Real.log_mul (norm_ne_zero_iff.mpr hc)
    (norm_ne_zero_iff.mpr (movingMonomial_ne_zero K y n α)), norm_movingMonomial_eq_prod]
  rw [Real.log_prod (fun i _ => zpow_ne_zero _ (norm_ne_zero_iff.mpr (y i.val).ne_zero))]
  simp only [Real.log_zpow, mul_neg, Finset.sum_neg_distrib]
  ring

/-- Each nonzero actual moving-basis coordinate term has its formal monomial order. -/
theorem order_movingTowerBasis_term_eq_sum (y : ℕ → Eˣ)
    (hy : ∀ i, IsAlgebraic K (y i : E)) (n : ℕ)
    (β : WindowExponent (fun i : Fin n => movingDegree K y i.val))
    (c : K) (hc : c ≠ 0) :
    -Real.log ‖c • movingTowerBasis K y hy n β‖ =
      -Real.log ‖c‖ + ∑ i : Fin n, (β.val i : ℝ) * (-Real.log ‖(y i.val : E)‖) := by
  have he : movingTowerBasis K y hy n β = movingMonomial K y n β.val := by
    apply Subtype.ext
    rw [movingTowerBasis_apply, movingMonomial_coe]
  rw [he]
  exact order_movingMonomial_eq_sum K y n β.val c hc

end HereditaryAtomicity.DVRBase
