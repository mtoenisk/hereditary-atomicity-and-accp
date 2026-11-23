import UnconditionalCounterexample.Variations.GuardTupleLifts
import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
import Mathlib.Analysis.Normed.Algebra.Ultra

/-!
# Agreement of analytic and integral guard conditions

The spectral norm extends the p-adic norm. The Witt integer ring is a
finite module, so all its elements, and in particular all powers of any
one of them, have uniformly bounded norm. Its uniformizer has norm p⁻¹.
Thus its discrete valuation and the analytic norm have the same unit ball.
-/

noncomputable section

namespace UnconditionalCounterexample.Variations.GuardUnramified

open WithZero

variable (p : ℕ) [Fact p.Prime] (k : Type*) [Field k] [CharP k p] [Algebra (ZMod p) k] [Finite k]

noncomputable instance : NontriviallyNormedField (LocalField p k) :=
  spectralNorm.nontriviallyNormedField ℚ_[p] _
noncomputable instance : NormedAlgebra ℚ_[p] (LocalField p k) := spectralNorm.normedAlgebra _ _
instance : IsUltrametricDist (LocalField p k) := IsUltrametricDist.of_normedAlgebra ℚ_[p]

theorem norm_witt_le_one (w : WittVector p k) :
    ‖algebraMap _ (LocalField p k) w‖ ≤ 1 := by
  classical
  let := Fintype.ofFinite k
  let O := WittVector p k
  let L := LocalField p k
  let j := algebraMap O L
  let lift := WittVector.teichmuller p (R := k)
  let C := ∑ c : k, ‖j (lift c)‖
  have hbound (v : O) : ‖j v‖ ≤ C := by
    obtain ⟨a, rfl⟩ := span_lifts p k lift (WittVector.teichmuller_coeff_zero p) v
    rw [map_sum]
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro i _
    rw [Algebra.smul_def, map_mul, norm_mul]
    apply mul_le_of_le_one_left (norm_nonneg _)
    change ‖algebraMap O L (algebraMap ℤ_[p] O (a i))‖ ≤ 1
    rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply ℤ_[p] ℚ_[p] L, norm_algebraMap']
    exact (a i).property
  by_contra! h
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt C h
  exact hn.not_ge (by simpa [j] using hbound (w^n))

theorem norm_le_one_iff_valuation (x : LocalField p k) :
    ‖x‖ ≤ 1 ↔ valuation p k x ≤ 1 := by
  let L := LocalField p k
  let v := valuation p k
  have hnorm (y : L) (hy : v y ≤ 1) : ‖y‖ ≤ 1 := by
    obtain ⟨w, rfl⟩ := (integral_iff p k _).mp hy
    exact norm_witt_le_one p k w
  refine ⟨fun h => ?_, hnorm x⟩
  by_contra! hlarge
  change 1 < v x at hlarge
  have hn : v x ≠ 0 := (zero_lt_one.trans hlarge).ne'
  have hx : x ≠ 0 := fun eq => hn (eq ▸ v.map_zero)
  have hlog : 0 < log (v x) := (lt_log_iff_exp_lt hn).mpr (by simpa using hlarge)
  have hsmall : v (p * x : L)⁻¹ ≤ 1 := by
    rw [map_inv₀, map_mul, show v (p : L) = _ from valuation_prime p k,
      ← exp_log hn, ← exp_add, ← exp_neg, exp_le_one_iff]
    omega
  have hle := hnorm _ hsmall
  have hpos : 0 < ‖(p : L) * x‖ := norm_pos_iff.mpr
    (mul_ne_zero (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero) hx)
  have hp : ‖(p : L)‖ < 1 := by
    rw [← map_natCast (algebraMap ℚ_[p] L) p, norm_algebraMap']
    exact Padic.norm_p_lt_one
  rw [norm_inv] at hle
  exact (not_lt_of_ge ((inv_le_one₀ hpos).mp hle)) (by
    rw [norm_mul]
    exact (mul_le_of_le_one_right (norm_nonneg _) h).trans_lt hp)

end UnconditionalCounterexample.Variations.GuardUnramified
