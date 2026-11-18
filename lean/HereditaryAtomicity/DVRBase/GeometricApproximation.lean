import HereditaryAtomicity.DVRBase.Gauss
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Algebra.Ring.GeomSum

/-!
# Finite geometric approximation modulo a near-junk ring

A finite geometric approximation gives the stated order bound under the specified ring
multiplication condition. Multiplicative values allow the bound to include zero.
-/

noncomputable section
namespace HereditaryAtomicity.DVRBase
open scoped BigOperators NNReal Topology
open Filter

variable {A : Type*} [CommRing A]

/-- Factoring a power difference retains the size of the actual difference. -/
theorem valuation_pow_sub_pow_le (v : Valuation A ℝ≥0) (d j : A)
    (hj : v j ≤ v d) (m : ℕ) :
    v (d ^ (m + 1) - j ^ (m + 1)) ≤ v (d - j) * v d ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
      have heq : d ^ (m + 1 + 1) - j ^ (m + 1 + 1) =
          (d - j) * d ^ (m + 1) + j * (d ^ (m + 1) - j ^ (m + 1)) := by
        simp only [pow_succ]
        ring
      rw [heq]
      apply v.map_add_le
      · simp only [map_mul, map_pow]
        exact le_rfl
      · rw [map_mul]
        calc
          v j * v (d ^ (m + 1) - j ^ (m + 1)) ≤
              v d * (v (d - j) * v d ^ m) := mul_le_mul' hj ih
          _ = v (d - j) * v d ^ (m + 1) := by ring

/-- Removing the constant and linear terms of the geometric sums gives an
error bounded by the difference times one additional small factor. -/
theorem valuation_geometric_tail_le (v : Valuation A ℝ≥0) (d j : A)
    (hj : v j ≤ v d) (hd : v d ≤ 1) (m : ℕ) :
    v (∑ i ∈ Finset.range m, (d ^ (i + 2) - j ^ (i + 2))) ≤
      v (d - j) * v d := by
  apply v.map_sum_le
  intro i _hi
  calc
    v (d ^ (i + 2) - j ^ (i + 2)) ≤ v (d - j) * v d ^ (i + 1) :=
      valuation_pow_sub_pow_le v d j hj (i + 1)
    _ ≤ v (d - j) * v d := by
      apply mul_le_mul_of_nonneg_left _ zero_le
      rw [pow_succ]
      exact (mul_le_mul_of_nonneg_right (pow_le_one₀ (n := i) zero_le hd) zero_le).trans_eq (one_mul _)

private theorem geometric_sum_split (d : A) (m : ℕ) :
    (∑ i ∈ Finset.range (m + 2), d ^ i) =
      1 + d + ∑ i ∈ Finset.range m, d ^ (i + 2) := by
  rw [Nat.add_comm m 2, Finset.sum_range_add]
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, pow_zero,
    zero_add, pow_one]
  congr 1
  apply Finset.sum_congr rfl
  intro i _hi
  rw [Nat.add_comm 2 i]

/-- The geometric argument produces a model-ring term modulo an arbitrarily
small error relative to the bad part. `U` is the actual auxiliary ring from
G3 in its application; it need not be contained in `R`.

This is the finite approximation used to match low terms, not a conclusion
that a valuation limit belongs to `R`. -/
theorem exists_geometric_ring_approximation
    (v : Valuation A ℝ≥0) (R U : Subring A)
    (ψ ρ Y e d j b : A) (hρ : ρ ∈ R) (hY : Y ∈ R) (he : e ∈ R)
    (hYU : ∀ x ∈ U, Y * x ∈ R) (hjU : j ∈ U)
    (hdb : d = j + b) (hj : v j ≤ v d) (hd : v d < 1) (hev : v e < 1)
    (heq : (ψ + ρ) * (1 - d) = Y * (1 + e))
    (B : ℝ≥0) (hB : 0 < B) (hb : v (Y * b) ≤ B) :
    ∃ r ∈ R, v (ψ - Y * b - r) < B := by
  have ht : Tendsto (fun n : ℕ => v (ψ + ρ) * v d ^ n) atTop (𝓝 0) := by
    simpa using (NNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hd).const_mul (v (ψ + ρ))
  obtain ⟨m, hm⟩ := eventually_atTop.mp (ht.eventually (gt_mem_nhds hB))
  let s := ∑ i ∈ Finset.range (m + 2), d ^ i
  let y := j + ∑ i ∈ Finset.range m, j ^ (i + 2)
  let h := ∑ i ∈ Finset.range m, (d ^ (i + 2) - j ^ (i + 2))
  have hy : y ∈ U := U.add_mem hjU (U.sum_mem (fun _ _ => U.pow_mem hjU _))
  have hs : s = 1 + b + y + h := by
    dsimp [s, y, h]
    rw [geometric_sum_split, Finset.sum_sub_distrib, hdb]
    ring
  have hsgeom : (1 - d) * s = 1 - d ^ (m + 2) := mul_neg_geom_sum d (m + 2)
  let r := Y * (1 + e) * (1 + y) - ρ
  have hr : r ∈ R := by
    have hr_eq : r = Y * (1 + e) + (1 + e) * (Y * y) - ρ := by dsimp [r]; ring
    rw [hr_eq]
    exact R.sub_mem (R.add_mem (R.mul_mem hY (R.add_mem R.one_mem he))
      (R.mul_mem (R.add_mem R.one_mem he) (hYU y hy))) hρ
  refine ⟨r, hr, ?_⟩
  have hid : ψ - Y * b - r =
      Y * e * b + Y * (1 + e) * h + (ψ + ρ) * d ^ (m + 2) := by
    have heqs := congrArg (fun x : A => x * s) heq
    rw [mul_assoc, hsgeom, hs] at heqs
    dsimp [r]
    linear_combination heqs
  rw [hid]
  apply v.map_add_lt
  · apply v.map_add_lt
    · rw [map_mul, map_mul]
      have hvb : v Y * v b ≤ B := by simpa using hb
      calc
        v Y * v e * v b = (v Y * v b) * v e := by ring
        _ ≤ B * v e := mul_le_mul_of_nonneg_right hvb zero_le
        _ < B := (mul_lt_mul_of_pos_left hev hB).trans_eq (mul_one B)
    · have hdh : d - j = b := by rw [hdb]; ring
      have hvh : v h ≤ v b * v d := by
        simpa only [h, hdh] using valuation_geometric_tail_le v d j hj hd.le m
      have hve : v (1 + e) ≤ 1 := v.map_add_le (by simp) hev.le
      rw [map_mul, map_mul]
      calc
        v Y * v (1 + e) * v h ≤ v Y * 1 * (v b * v d) :=
          mul_le_mul' (mul_le_mul_of_nonneg_left hve zero_le) hvh
        _ = v (Y * b) * v d := by rw [map_mul]; ring
        _ ≤ B * v d := mul_le_mul_of_nonneg_right hb zero_le
        _ < B := (mul_lt_mul_of_pos_left hd hB).trans_eq (mul_one B)
  · simpa only [map_mul, map_pow] using hm (m + 2) (by omega)

end HereditaryAtomicity.DVRBase
