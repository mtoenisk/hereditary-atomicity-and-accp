import HereditaryAtomicity.DVRBase.MovingWindows
import HereditaryAtomicity.DVRBase.PowerWindow
import Mathlib.RingTheory.AlgebraTower

/-!
# Bases indexed by the moving exponent windows

A consecutive power basis and a twist at each step construct the moving tower basis.
The coordinate estimate propagates the preceding level's bound.
-/

noncomputable section
namespace HereditaryAtomicity.DVRBase

open scoped BigOperators

section PowerBasis

variable {K L : Type*} [NormedField K] [Field L] [Algebra K L]

/-- The power basis indexed by the literal centered integer degree window. -/
def centeredPowerBasis (b : PowerBasis K L) (hy : b.gen ≠ 0) :
    Module.Basis (digitInterval b.dim) K L :=
  (powerWindowBasis b hy (-(b.dim / 2 : ℕ))).reindex (digitIntervalEquivFin b.dim).symm

@[simp] theorem centeredPowerBasis_apply (b : PowerBasis K L) (hy : b.gen ≠ 0)
    (j : digitInterval b.dim) : centeredPowerBasis b hy j = b.gen ^ j.val := by
  simp only [centeredPowerBasis, Module.Basis.reindex_apply, Equiv.symm_symm,
    powerWindowBasis_apply]
  congr 1
  rw [digitIntervalEquivFin_val]
  omega

end PowerBasis

section Tower

variable {ι J K L E : Type*} [Field K] [Field L] [Field E]
  [Algebra K L] [Algebra L E] [Algebra K E] [IsScalarTower K L E]

/-- A scalar tower basis with an independently chosen unit twist in each top-level slot. -/
def twistedTowerBasis (b : Module.Basis ι K L) (c : Module.Basis J L E)
    (w : J → Lˣ) : Module.Basis (ι × J) K E :=
  b.smulTower (c.unitsSMul w)

@[simp] theorem twistedTowerBasis_apply (b : Module.Basis ι K L)
    (c : Module.Basis J L E) (w : J → Lˣ) (ij : ι × J) :
    twistedTowerBasis b c w ij = b ij.1 • (w ij.2 • c ij.2) := by
  simp only [twistedTowerBasis, Module.Basis.smulTower_apply, Module.Basis.unitsSMul_apply]

@[simp] theorem twistedTowerBasis_repr (b : Module.Basis ι K L)
    (c : Module.Basis J L E) (w : J → Lˣ) (x : E) (ij : ι × J) :
    (twistedTowerBasis b c w).repr x ij =
      b.repr ((w ij.2)⁻¹ • c.repr x ij.2) ij.1 := by
  simp only [twistedTowerBasis, Module.Basis.smulTower_repr, Module.Basis.repr_unitsSMul]

/-- Rescaling a basis does not change its individual coordinate-times-vector terms. -/
theorem unitsSMul_basis_term (c : Module.Basis J L E) (w : J → Lˣ) (x : E) (j : J) :
    (c.unitsSMul w).repr x j • (c.unitsSMul w) j = c.repr x j • c j := by
  rw [Module.Basis.repr_unitsSMul, Module.Basis.unitsSMul_apply]
  simp only [Units.smul_def, smul_eq_mul, smul_smul]
  congr 1
  rw [mul_right_comm, Units.inv_mul, one_mul]

/-- One moving-basis induction step. The twist is the inverse pole power of
the product of all earlier generators. -/
def movingBasisStep {N : ℕ} (D : Fin (N + 1) → ℕ)
    (b : Module.Basis (WindowExponent (fun i : Fin N => D i.castSucc)) K L)
    (c : Module.Basis (digitInterval (D (Fin.last N))) L E) (q : Lˣ) :
    Module.Basis (WindowExponent D) K E :=
  (twistedTowerBasis b c (fun j => q ^ (-max 0 (-j.val)))).reindex (windowSuccEquiv D).symm

@[simp] theorem movingBasisStep_apply {N : ℕ} (D : Fin (N + 1) → ℕ)
    (b : Module.Basis (WindowExponent (fun i : Fin N => D i.castSucc)) K L)
    (c : Module.Basis (digitInterval (D (Fin.last N))) L E) (q : Lˣ)
    (β : WindowExponent D) :
    movingBasisStep D b c q β = b ((windowSuccEquiv D β).1) •
      (q ^ (-max 0 (-β.val (Fin.last N))) • c ((windowSuccEquiv D β).2)) := by
  simp only [movingBasisStep, Module.Basis.reindex_apply, Equiv.symm_symm,
    twistedTowerBasis_apply]
  rfl

/-- A common translation of all exponents is multiplication by a power of
the product of the generators, and the inverse translation cancels exactly. -/
theorem prod_zpow_shift_cancel {ι G : Type*} [Fintype ι] [CommGroup G]
    (y : ι → G) (β : ι → ℤ) (a : ℤ) :
    (∏ i, y i ^ (β i + a)) * (∏ i, y i) ^ (-a) = ∏ i, y i ^ β i := by
  simp only [zpow_add, Finset.prod_mul_distrib, Finset.prod_zpow]
  rw [mul_assoc, ← zpow_add, add_neg_cancel, zpow_zero, mul_one]

/-- The tower-basis step is the literal monomial with its uncorrected exponents.
The translation in the smaller window is exactly canceled by the slot twist. -/
theorem movingBasisStep_apply_monomial {N : ℕ} (D : Fin (N + 1) → ℕ)
    (b : Module.Basis (WindowExponent (fun i : Fin N => D i.castSucc)) K L)
    (c : Module.Basis (digitInterval (D (Fin.last N))) L E)
    (y : Fin N → Lˣ) (z : E)
    (hb : ∀ γ, b γ = ((∏ i, y i ^ γ.val i : Lˣ) : L))
    (hc : ∀ j, c j = z ^ j.val) (β : WindowExponent D) :
    movingBasisStep D b c (∏ i, y i) β =
      algebraMap L E ((∏ i, y i ^ β.val i.castSucc : Lˣ) : L) *
        z ^ β.val (Fin.last N) := by
  rw [movingBasisStep_apply, hb, hc]
  change (((∏ i, y i ^ (β.val i.castSucc + poleTail β.val N) : Lˣ) : L)) •
      (((∏ i, y i) ^ (-max 0 (-β.val (Fin.last N)))) • z ^ β.val (Fin.last N)) = _
  rw [poleTail_last, Units.smul_def, ← mul_smul, Algebra.smul_def, ← Units.val_mul,
    prod_zpow_shift_cancel]

end Tower

section NormBounds

variable {ι J K L E : Type*} [NormedField K] [NormedField L] [NormedField E]
  [NormedAlgebra K L] [NormedAlgebra L E] [NormedAlgebra K E] [IsScalarTower K L E]

/-- A lossless top-level expansion retains the coordinate bound of the previous
basis through every independent unit twist. This is the mechanism of the monomial basis bound. -/
theorem norm_twistedTowerBasis_term_le (b : Module.Basis ι K L)
    (c : Module.Basis J L E) (w : J → Lˣ) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ z : L, ∀ i : ι, ‖b.repr z i • b i‖ ≤ C * ‖z‖)
    (x : E) (hc : ∀ j : J, ‖c.repr x j • c j‖ ≤ ‖x‖) (ij : ι × J) :
    ‖(twistedTowerBasis b c w).repr x ij • twistedTowerBasis b c w ij‖ ≤ C * ‖x‖ := by
  let c' := c.unitsSMul w
  change ‖(b.smulTower c').repr x ij • (b.smulTower c') ij‖ ≤ _
  rw [Module.Basis.smulTower_repr, Module.Basis.smulTower_apply, ← smul_assoc]
  rw [norm_smul]
  calc
    ‖b.repr (c'.repr x ij.2) ij.1 • b ij.1‖ * ‖c' ij.2‖ ≤
        (C * ‖c'.repr x ij.2‖) * ‖c' ij.2‖ :=
      mul_le_mul_of_nonneg_right (hb _ _) (norm_nonneg _)
    _ = C * ‖c'.repr x ij.2 • c' ij.2‖ := by rw [norm_smul]; ring
    _ = C * ‖c.repr x ij.2 • c ij.2‖ := by rw [unitsSMul_basis_term]
    _ ≤ C * ‖x‖ := mul_le_mul_of_nonneg_left (hc ij.2) hC

/-- The same previous-level bound after the exact moving-window reindexing. -/
theorem norm_movingBasisStep_term_le {N : ℕ} (D : Fin (N + 1) → ℕ)
    (b : Module.Basis (WindowExponent (fun i : Fin N => D i.castSucc)) K L)
    (c : Module.Basis (digitInterval (D (Fin.last N))) L E) (q : Lˣ)
    {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ z : L, ∀ i, ‖b.repr z i • b i‖ ≤ C * ‖z‖)
    (x : E) (hc : ∀ j, ‖c.repr x j • c j‖ ≤ ‖x‖) (β : WindowExponent D) :
    ‖(movingBasisStep D b c q).repr x β • movingBasisStep D b c q β‖ ≤ C * ‖x‖ := by
  simpa only [movingBasisStep, Module.Basis.repr_reindex_apply, Module.Basis.reindex_apply,
    Equiv.symm_symm] using norm_twistedTowerBasis_term_le b c
      (fun j => q ^ (-max 0 (-j.val))) hC hb x hc (windowSuccEquiv D β)

end NormBounds

section CompletePowerBasis

variable {K L : Type*} [NontriviallyNormedField K] [CompleteSpace K]
  [IsUltrametricDist K] [NormedField L] [NormedAlgebra K L]
  [Algebra.IsAlgebraic K L]

/-- Integer-indexed form of the lossless monomial estimate for the centered power basis. -/
theorem norm_centeredPowerBasis_monomial_term_le (b : PowerBasis K L) (hy : b.gen ≠ 0)
    (c : K) (a : ℤ) (j : digitInterval b.dim) :
    ‖(centeredPowerBasis b hy).repr (c • b.gen ^ a) j • centeredPowerBasis b hy j‖ ≤
      ‖c • b.gen ^ a‖ := by
  simpa only [centeredPowerBasis, Module.Basis.repr_reindex_apply,
    Module.Basis.reindex_apply, Equiv.symm_symm] using
    norm_powerWindowBasis_monomial_term_le b hy c (-(b.dim / 2 : ℕ)) a
      (digitIntervalEquivFin b.dim j)

end CompletePowerBasis

end HereditaryAtomicity.DVRBase
