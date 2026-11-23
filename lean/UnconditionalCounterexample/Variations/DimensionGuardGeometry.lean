import UnconditionalCounterexample.Variations.GuardNorm
import UnconditionalCounterexample.Variations.DimensionClosedPoints
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra

namespace UnconditionalCounterexample.Variations.GuardUnramified

open MvPolynomial

variable {p : ℕ} [Fact p.Prime] {k : Type*} [Field k] [CharP k p] [Algebra (ZMod p) k] [Finite k]
variable {r : ℕ}

theorem adjoin_tuple_eq_top (w : Fin (r+1) → WittVector p k)
    (hgen : Algebra.adjoin ℤ_[p] ({w 0} : Set (WittVector p k)) = ⊤) :
    Algebra.adjoin ℚ_[p] (Set.range fun j ↦ algebraMap _ (LocalField p k) (w j)) = ⊤ := by
  let L := LocalField p k
  let O := WittVector p k
  let S := IntermediateField.adjoin ℚ_[p] (Set.range fun j ↦ algebraMap O L (w j))
  let φ := IsScalarTower.toAlgHom ℤ_[p] O L
  have hint (v : O) : algebraMap O L v ∈ S := by
    let U := (S.toSubalgebra.restrictScalars ℤ_[p]).comap φ
    have hu : Algebra.adjoin ℤ_[p] ({w 0} : Set O) ≤ U := by
      apply Algebra.adjoin_le
      intro a ha
      obtain rfl := Set.mem_singleton_iff.mp ha
      exact IntermediateField.subset_adjoin _ _ ⟨0, rfl⟩
    exact hu (hgen ▸ Algebra.mem_top)
  apply top_unique
  intro z _
  obtain ⟨x, y, _, hy⟩ := IsFractionRing.div_surjective (A := O) z
  rw [← IntermediateField.adjoin_toSubalgebra]
  change z ∈ S
  rw [← hy]
  exact S.div_mem (hint x) (hint y)

theorem first_ne_scalar (w : WittVector p k)
    (hout : w.coeff 0 ∉ Set.range (algebraMap (ZMod p) k)) (x : ℚ_[p]) :
    algebraMap _ (LocalField p k) w ≠ algebraMap ℚ_[p] _ x := by
  intro he
  have hx : ‖x‖ ≤ 1 := by
    rw [← norm_algebraMap' (LocalField p k) x, ← he]
    exact norm_witt_le_one _ _ w
  let a : ℤ_[p] := ⟨x,hx⟩
  have h : w = algebraMap ℤ_[p] (WittVector p k) a := by
    apply IsFractionRing.injective (WittVector p k) (LocalField p k)
    rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply ℤ_[p] ℚ_[p] (LocalField p k)]
    exact he
  exact hout ⟨((WittVector.equiv p).symm a).coeff 0, by rw [h]; rfl⟩

end UnconditionalCounterexample.Variations.GuardUnramified
