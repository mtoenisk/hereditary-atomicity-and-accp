import HereditaryAtomicity.DVRBase.SourceSupport
import HereditaryAtomicity.DVRBase.SourceCertificateCore

/-!
# Fresh return to an intersection of maximal stalks

Division by later ratios proves absence of atoms in the specified source subset. The
argument allows arbitrary sets of maximal ideals and checks each quotient in the
source domain.
-/

noncomputable section
namespace HereditaryAtomicity.DVRBase
open scoped BigOperators
universe u
variable {K : Type u} [Field K]
namespace SourceBlockData
variable {R : Subring K} (B : SourceBlockData R)

/-- The arbitrarily fresh quotient from the literal junk ideal returns to the
original source when its selected ratios have support in the chosen places. -/
theorem sourceJunk_fresh_split_in_intersection
    (D : Subring K) [IsFractionRing D K] (places : Set (MaximalSpectrum D))
    (O : Subring K) (hO : ∀ a : O, B.valuation (a : K) ≤ 1)
    (Λ : Set ℕ) (hcofinal : ∀ N : ℕ, ∃ m, N ≤ m ∧ m ∈ Λ)
    (hS : ∀ M ∈ places, B.sourceSubring O Λ ≤ sourceMaximalStalk D M)
    (sourceRatio : ℕ → D) (hratio : ∀ n, (sourceRatio n : K) = (B.ratio n : K))
    (hunits : ∀ n (M : MaximalSpectrum D), M ∉ places →
      IsUnit (sourceMaximalMap D M (sourceRatio n)))
    {g : K} (hg : g ∈ B.sourceJunk O) (hgD : g ∈ D) (hg0 : g ≠ 0) (N : ℕ) :
    ∃ n : ℕ, N ≤ n ∧ n ∈ Λ ∧ ∃ q : K,
      q ∈ B.sourceJunk O ∧ q ∈ D ∧ g = (sourceRatio n : K) * q ∧
      (sourceRatio n : K) ∈ B.sourceSubring O Λ ∧
      0 < realValuationOrder B.valuation (sourceRatio n : K) ∧
      0 < realValuationOrder B.valuation q := by
  obtain ⟨n, hn, hnΛ, q, hq, heq, hy, hypos, hqpos⟩ :=
    B.sourceJunk_fresh_split O hO Λ hcofinal hg hg0 N
  have hy0 : (sourceRatio n : K) ≠ 0 := by
    rw [hratio]
    exact Subtype.coe_ne_coe.mpr (B.ratio_ne_zero n)
  have heq' : g = (sourceRatio n : K) * q := by rwa [hratio n]
  have hquot : g / (sourceRatio n : K) = q := by
    rw [heq', mul_div_cancel_left₀ _ hy0]
  have hqD : q ∈ D := by
    rw [← hquot]
    apply source_div_mem_of_stalks_and_units D places hgD (sourceRatio n) _ (hunits n)
    intro M hM
    rw [hquot]
    exact hS M hM (B.sourceJunk_le_sourceSubring O Λ hq)
  exact ⟨n, hn, hnΛ, q, hq, hqD, heq', by rwa [hratio], by rwa [hratio], hqpos⟩

/-- The actual intersection source is nonatomic. Fresh quotient membership is
proved from stalk containment and the support condition on the selected ratios. -/
theorem not_isAtomicDomain_intersection_of_no_factorization
    (D : Subring K) [IsFractionRing D K] (places : Set (MaximalSpectrum D))
    (O : Subring K) (hO : ∀ a : O, B.valuation (a : K) ≤ 1)
    (Λ : Set ℕ) (hcofinal : ∀ N : ℕ, ∃ m, N ≤ m ∧ m ∈ Λ)
    (hS : ∀ M ∈ places, B.sourceSubring O Λ ≤ sourceMaximalStalk D M)
    (sourceRatio : ℕ → D) (hratio : ∀ n, (sourceRatio n : K) = (B.ratio n : K))
    (hunits : ∀ n (M : MaximalSpectrum D), M ∉ places →
      IsUnit (sourceMaximalMap D M (sourceRatio n)))
    (hzD : (B.endpoint 1 : K) ∈ D)
    (hno : B.NoOutsideJunkFactorization O Λ) :
    ¬ Factorization.IsAtomicDomain ↥(B.sourceSubring O Λ ⊓ D) := by
  let S := B.sourceSubring O Λ
  have hbound : ∀ a : ↥(S ⊓ D), B.valuation (a : K) ≤ 1 :=
    fun a => B.sourceSubring_bounded O hO Λ ⟨a, a.property.1⟩
  have hunit : ∀ a : ↥(S ⊓ D), (a : K) ∈ B.sourceJunk O → ¬ IsUnit a := by
    intro a ha
    by_cases ha0 : a = 0
    · simpa only [ha0] using (not_isUnit_zero : ¬ IsUnit (0 : ↥(S ⊓ D)))
    · exact not_isUnit_of_mapped_order_pos (S ⊓ D).subtype B.valuation hbound
        (B.sourceJunk_order_pos O hO ha (Subtype.coe_ne_coe.mpr ha0))
  have hsplit : ∀ a : ↥(S ⊓ D), (a : K) ∈ B.sourceJunk O →
      ∃ b c : ↥(S ⊓ D), ¬ IsUnit b ∧ ¬ IsUnit c ∧ a = b * c := by
    intro a ha
    by_cases ha0 : a = 0
    · exact ⟨0, 0, not_isUnit_zero, not_isUnit_zero, by simp [ha0]⟩
    obtain ⟨n, _, _, q, hq, hqD, heq, hy, hypos, hqpos⟩ :=
      B.sourceJunk_fresh_split_in_intersection D places O hO Λ hcofinal hS
        sourceRatio hratio hunits ha a.property.2 (Subtype.coe_ne_coe.mpr ha0) 0
    let b : ↥(S ⊓ D) := ⟨sourceRatio n, hy, (sourceRatio n).property⟩
    let c : ↥(S ⊓ D) := ⟨q, B.sourceJunk_le_sourceSubring O Λ hq, hqD⟩
    exact ⟨b, c, not_isUnit_of_mapped_order_pos (S ⊓ D).subtype B.valuation hbound hypos,
      not_isUnit_of_mapped_order_pos (S ⊓ D).subtype B.valuation hbound hqpos,
      Subtype.ext heq⟩
  apply not_isAtomicDomain_intersection S D (B.sourceJunk O)
    (Subtype.coe_ne_coe.mpr (B.endpoint_ne_zero 1))
    (B.endpoint_mem_sourceSubring O Λ 1) hzD hunit hsplit
  intro ι _ f hprod hout
  let e := Fintype.equivFin ι
  apply hno (Fintype.card ι) (fun i => (f (e.symm i) : K))
    (fun i => (f (e.symm i)).property) (fun i => hout (e.symm i))
  exact (e.symm.prod_comp (fun i => (f i : K))).trans
    (by simpa only [map_prod, Subring.subtype_apply] using congrArg S.subtype hprod)

/-- The initial-segment generator test discharges every selected-stalk
containment premise in the intersection theorem. The obstruction certificate
is the only remaining model input at this algebraic interface. -/
theorem not_isAtomicDomain_intersection_of_initial_segment
    (D : Subring K) [IsFractionRing D K] (places : Set (MaximalSpectrum D))
    (O : Subring K) (hO : ∀ a : O, B.valuation (a : K) ≤ 1)
    (hOA : ∀ M ∈ places, O ≤ sourceMaximalStalk D M)
    (hπ : (B.uniformizer : K) ∈ O)
    (sourceEndpoint sourceRatio : ℕ → D)
    (hendpoint : ∀ n, (sourceEndpoint n : K) = (B.endpoint n : K))
    (hratio : ∀ n, (sourceRatio n : K) = (B.ratio n : K))
    (hunits : ∀ n (M : MaximalSpectrum D), M ∉ places →
      IsUnit (sourceMaximalMap D M (sourceRatio n)))
    (hreturn : ∀ M ∈ places, ∀ l, sourceEndpoint l ∈ M.asIdeal →
      ∀ i < l, (B.ratio i : K) ^ B.returnExponent i /
        (B.uniformizer : K) ^ B.exponent ∈ sourceMaximalStalk D M)
    (Λ : Set ℕ) (hcofinal : ∀ N : ℕ, ∃ m, N ≤ m ∧ m ∈ Λ)
    (hno : B.NoOutsideJunkFactorization O Λ) :
    ¬ Factorization.IsAtomicDomain ↥(B.sourceSubring O Λ ⊓ D) := by
  have hz (M : MaximalSpectrum D) (n : ℕ) :
      (B.endpoint n : K) ∈ sourceMaximalStalk D M := by
    rw [← hendpoint]
    exact le_sourceMaximalStalk D M (sourceEndpoint n).property
  have hy (M : MaximalSpectrum D) (n : ℕ) :
      (B.ratio n : K) ∈ sourceMaximalStalk D M := by
    rw [← hratio]
    exact le_sourceMaximalStalk D M (sourceRatio n).property
  have hS : ∀ M ∈ places, B.sourceSubring O Λ ≤ sourceMaximalStalk D M := by
    intro M hM
    apply (B.sourceSubring_le_sourceRing O Λ).trans
    apply B.sourceRing_le_of_initial_segment O _ (hOA M hM) hπ (hz M) (hy M)
    intro l hu i hi
    apply hreturn M hM l _ i hi
    by_contra he
    apply hu
    have hh := (isUnit_sourceMaximalMap_iff D M (sourceEndpoint l)).mpr he
    convert hh using 1
    apply Subtype.ext
    exact (hendpoint l).symm
  apply B.not_isAtomicDomain_intersection_of_no_factorization D places O hO Λ hcofinal
    hS sourceRatio hratio hunits _ hno
  rw [← hendpoint]
  exact (sourceEndpoint 1).property

end SourceBlockData
end HereditaryAtomicity.DVRBase
