import HereditaryAtomicity.DVRBase.SourceDomination
import HereditaryAtomicity.DVRBase.CoefficientExtension

/-!
# Common coefficients and dead quotients at one place

At each place separately, choose the first level at which the quotient reaches the
threshold. Coefficients pass between the rings by inclusion.
-/
noncomputable section
namespace HereditaryAtomicity.DVRBase
open scoped BigOperators NNReal
variable {K : Type*} [Field K]

def coefficientFractionMap {O₀ O : Subring K} (h : O₀ ≤ O) :
    FractionRing O₀ →+* FractionRing O :=
  IsFractionRing.lift (g := (algebraMap O (FractionRing O)).comp (Subring.inclusion h))
    ((IsFractionRing.injective O (FractionRing O)).comp (Subring.inclusion_injective h))

@[simp] theorem coefficientFractionMap_algebraMap {O₀ O : Subring K} (h : O₀ ≤ O) (a : O₀) :
    coefficientFractionMap h (algebraMap O₀ (FractionRing O₀) a) =
      algebraMap O (FractionRing O) (Subring.inclusion h a) :=
  IsFractionRing.lift_algebraMap _ a

@[simp] theorem coefficientFractionEmbedding_map {O₀ O : Subring K} (h : O₀ ≤ O)
    (a : FractionRing O₀) :
    coefficientFractionEmbedding O (coefficientFractionMap h a) =
      coefficientFractionEmbedding O₀ a := by
  have he : (coefficientFractionEmbedding O).comp (coefficientFractionMap h) =
      coefficientFractionEmbedding O₀ := by
    apply IsFractionRing.ringHom_ext (A := O₀)
    intro x
    simp
  exact RingHom.congr_fun he a

def deadQuotientExponent {n m : ℕ} (_hm : m ≤ n) (μ : Fin m → ℕ) : Fin n → ℤ :=
  fun i => if hi : i.val < m then (μ ⟨i.val, hi⟩ : ℤ) + 1 else 0

/-- The formal quotient cY^μ/Z_m, where the common endpoint has top z₀. -/
def deadQuotient {F : Type*} [Field F] {n m : ℕ} (hm : m ≤ n)
    (μ : Fin m → ℕ) (c z₀ : F) : Laurent F n :=
  AddMonoidAlgebra.single (deadQuotientExponent hm μ) (c / z₀)

namespace SourceBlockData
variable {R : Subring K} (D : SourceBlockData R)

/-- Every dead quotient belongs to E_n, irrespective of its first dead level. -/
theorem deadQuotient_uniformizer_mem_formalRing (O : Subring K) (π : O) (hπ0 : π ≠ 0)
    {n m : ℕ} (hm : m ≤ n) (μ : Fin m → ℕ) (e : ℕ)
    (hd : ∃ l, l ≤ m ∧ D.DeadAt e μ l) :
    deadQuotient hm μ ((algebraMap O (FractionRing O) π) ^ e)
      ((algebraMap O (FractionRing O) π) ^ D.exponent) ∈ D.formalRing O π n := by
  classical
  have hp0 : algebraMap O (FractionRing O) π ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective O (FractionRing O))).mpr hπ0
  have hvar : ∀ i : Fin n, variableMonomial i ∈ D.formalRing O π n :=
    fun i => Subring.subset_closure (FormalGenerator.coordinate i)
  rcases D.exists_firstDead_prefix e μ hd with he | ⟨h, hl, he, hμ⟩
  · have hc : (algebraMap O (FractionRing O) π) ^ e /
        (algebraMap O (FractionRing O) π) ^ D.exponent =
        algebraMap O (FractionRing O) (π ^ (e - D.exponent)) := by
      rw [map_pow, pow_sub₀ _ hp0 he, div_eq_mul_inv]
    rw [deadQuotient, hc]
    apply single_nonneg_mem_subring _ hvar
    · intro i
      dsimp [deadQuotientExponent]
      split_ifs <;> positivity
    · exact Subring.subset_closure (FormalGenerator.coefficient _)
  · let hln := hl.trans hm
    let δ : Fin n → ℤ := deadQuotientExponent hm μ - h.formalExponent hln
    have hδ : ∀ i, 0 ≤ δ i := by
      intro i
      dsimp only [δ, Pi.sub_apply, deadQuotientExponent]
      rw [h.formalExponent_apply]
      split_ifs with hi hj hj
      · have hv := hμ ⟨i.val, hj⟩
        simp only [Fin.castLE_mk] at hv
        rw [hv]
        omega
      · simp only [sub_zero]
        positivity
      · omega
      · simp
    have hmon : AddMonoidAlgebra.single δ (1 : FractionRing O) ∈ D.formalRing O π n := by
      apply single_nonneg_mem_subring _ hvar δ hδ
      change (1 : Laurent (FractionRing O) n) ∈ D.formalRing O π n
      exact (D.formalRing O π n).one_mem
    have hfirst : h.formal O π hln ∈ D.formalRing O π n :=
      Subring.subset_closure (FormalGenerator.firstDead h hln)
    have hprod := (D.formalRing O π n).mul_mem hfirst hmon
    rw [h.formal_eq_single, AddMonoidAlgebra.single_mul_single, mul_one, he] at hprod
    have hsum : h.formalExponent hln + δ = deadQuotientExponent hm μ := by
      dsimp [δ]
      abel
    rwa [hsum] at hprod

/-- The same quotient with an arbitrary nonzero DVR coefficient and a unit-twisted top.
Deadness is expressed using the true coefficient order. -/
theorem deadQuotient_mem_formalRing (O : Subring K) [IsDiscreteValuationRing O]
    (π : O) (hπirr : Irreducible π) (hπ : (π : K) = (D.uniformizer : K))
    (hO : ∀ a : O, D.valuation (a : K) ≤ 1)
    {n m : ℕ} (hm : m ≤ n) (μ : Fin m → ℕ) (c : O) (hc : c ≠ 0)
    (u : Oˣ) (z₀ : FractionRing O)
    (hz₀ : z₀ = algebraMap O (FractionRing O) (u : O) *
      (algebraMap O (FractionRing O) π) ^ D.exponent)
    (hd : ∃ l, l ≤ m ∧ D.threshold l +
      remainingValue (fun i : Fin m => D.weight i.val) D.exponent l ≤
      partialValue (fun i : Fin m => D.weight i.val)
        (realValuationOrder D.valuation (c : K)) (fun i => (μ i : ℤ)) l) :
    deadQuotient hm μ (algebraMap O (FractionRing O) c) z₀ ∈ D.formalRing O π n := by
  obtain ⟨e, w, hce, _, hord, _⟩ := exists_normalized_dvr_coefficient_power O π hπirr
    D.valuation hO (hπ.symm ▸ D.normalized) c hc
  have he : c = (w : O) * π ^ e := Subtype.ext hce
  have hdead : ∃ l, l ≤ m ∧ D.DeadAt e μ l := by
    dsimp only [DeadAt]
    rwa [hord] at hd
  have hq := D.deadQuotient_uniformizer_mem_formalRing O π hπirr.ne_zero hm μ e hdead
  let a : O := (w : O) * (↑(u⁻¹) : O)
  have ha : AddMonoidAlgebra.single (0 : Fin n → ℤ)
      (algebraMap O (FractionRing O) a) ∈ D.formalRing O π n :=
    Subring.subset_closure (FormalGenerator.coefficient a)
  convert (D.formalRing O π n).mul_mem ha hq using 1
  dsimp only [deadQuotient]
  rw [AddMonoidAlgebra.single_mul_single, zero_add, he, map_mul, map_pow, hz₀]
  congr 1
  dsimp [a]
  simp only [map_mul]
  have hu : algebraMap O (FractionRing O) (u : O) *
      algebraMap O (FractionRing O) (↑(u⁻¹) : O) = 1 := by
    rw [← map_mul]
    simp
  field_simp
  rw [mul_assoc, hu, mul_one]

end SourceBlockData
end HereditaryAtomicity.DVRBase
