import HereditaryAtomicity.DVRBase.CoefficientExtension
import HereditaryAtomicity.DVRBase.KernelIdeal
import HereditaryAtomicity.DVRBase.MovingLift

noncomputable section
namespace HereditaryAtomicity.DVRBase
open scoped NNReal
variable {k l : Type*} [Field k] [Field l] {n : ℕ}

/-- The exact Z₁J₀ target, like every coefficient support class, is preserved
and reflected by an actual valuation-preserving coefficient embedding. -/
theorem laurentMap_mem_modelKernelJunk_iff (f : k →+* l) (v : Valuation k ℝ≥0)
    (w : Valuation l ℝ≥0) (hv : ∀ c, w (f c) = v c)
    (π : k) (hπ0 : π ≠ 0) (hπ : realValuationOrder v π = 1)
    (P : ModelParameters n) (p : Laurent k n) :
    laurentMap f n p ∈ modelKernelJunk w (f π) P ↔ p ∈ modelKernelJunk v π P := by
  have hfπ : realValuationOrder w (f π) = 1 := (realValuationOrder_map f v w hv π).trans hπ
  rw [modelKernelJunk_eq_supported w (f π) ((map_ne_zero_iff f f.injective).mpr hπ0) hfπ P,
    modelKernelJunk_eq_supported v π hπ0 hπ P]
  exact laurentMap_mem_supported_iff f v w hv _ p

end HereditaryAtomicity.DVRBase

noncomputable section
namespace HereditaryAtomicity.DVRBase
open scoped BigOperators NNReal
variable {K k E : Type*} [Field K] [NormedField k] [NormedField E] [NormedAlgebra k E]

/-- The actual moving-field evaluation has the same source value after
coefficient extension; the coefficient square and every ratio are explicit. -/
theorem movingTowerEval_map_coe_of_source
    {R : Subring K} (D : SourceBlockData R) (O : Subring K)
    (f : FractionRing O →+* k) (g : K →+* E) (y : ℕ → Eˣ)
    (hcoeff : (algebraMap k E).comp f = g.comp (coefficientFractionEmbedding O))
    (hy : ∀ i, (y i : E) = g (D.ratio i : K)) (n : ℕ)
    (p : Laurent (FractionRing O) n) :
    ((movingTowerEval k y n (laurentMap f n p) : movingField k y n) : E) =
      g (D.evaluation O n p) := by
  rw [movingTowerEval_coe, ← AddMonoidAlgebra.sum_coeff_single p, Finsupp.sum]
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro β _
  have hc := DFunLike.congr_fun hcoeff (p.coeff β)
  simp only [RingHom.comp_apply] at hc
  simp only [laurentMap_single, eval_single, SourceBlockData.evaluation,
    laurentEvaluation_single, map_mul, map_prod, map_zpow₀, hc, monomial,
    MonoidHom.coe_mk, OneHom.coe_mk, Units.coe_prod, Units.val_zpow_eq_zpow_val, hy]
  rfl

/-- In particular, zero original evaluation gives zero in the actual moving
field, with no completion-kernel identification hypothesis. -/
theorem movingTowerEval_map_eq_zero_of_source
    {R : Subring K} (D : SourceBlockData R) (O : Subring K)
    (f : FractionRing O →+* k) (g : K →+* E) (y : ℕ → Eˣ)
    (hcoeff : (algebraMap k E).comp f = g.comp (coefficientFractionEmbedding O))
    (hy : ∀ i, (y i : E) = g (D.ratio i : K)) (n : ℕ)
    (p : Laurent (FractionRing O) n) (hp : D.evaluation O n p = 0) :
    movingTowerEval k y n (laurentMap f n p) = 0 := by
  apply Subtype.ext
  change ((movingTowerEval k y n (laurentMap f n p) : movingField k y n) : E) = 0
  rw [movingTowerEval_map_coe_of_source D O f g y hcoeff hy n p, hp, map_zero]

end HereditaryAtomicity.DVRBase
