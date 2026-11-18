import HereditaryAtomicity.DVRBase.FamilyReturn

/-!
# Initial-segment support and source-ring containment

Test the first-threshold quotient at its own endpoint. A unit endpoint supplies the
quotient directly. At a nonunit endpoint only the power returns from its finite prefix
are needed.
-/

noncomputable section
namespace HereditaryAtomicity.DVRBase
open scoped BigOperators
variable {K : Type*} [Field K]
namespace SourceBlockData
variable {R : Subring K} (D : SourceBlockData R)

/-- Lemma D needs return witnesses only for the variables actually occurring. -/
theorem large_monomial_mem_subring_prefix (A : Subring K)
    (hπ : (D.uniformizer : K) ∈ A) (l e : ℕ) (q : Fin l → ℕ)
    (hy : ∀ i : Fin l, (D.ratio i.val : K) ∈ A)
    (hreturn : ∀ i : Fin l,
      (D.ratio i.val : K) ^ D.returnExponent i.val /
        (D.uniformizer : K) ^ D.exponent ∈ A)
    (hlarge : D.threshold l ≤ (e : ℝ) - D.exponent +
      ∑ i : Fin l, (q i : ℝ) * D.weight i.val) :
    (D.uniformizer : K) ^ e / (D.uniformizer : K) ^ D.exponent *
      ∏ i : Fin l, (D.ratio i.val : K) ^ q i ∈ A := by
  let πA : A := ⟨D.uniformizer, hπ⟩
  let yA : Fin l → A := fun i => ⟨D.ratio i.val, hy i⟩
  exact large_monomial_mem_source A πA
    (fun h => D.uniformizer_ne_zero (Subtype.ext (congrArg A.subtype h))) yA
    D.exponent e (fun i => D.returnExponent i.val) q (fun i => D.weight i.val)
    hreturn (fun i => (D.ratio_order_pos i.val).le)
    (fun i => (D.weight_lt_exponent i.val).le) hlarge

/-- The unit-endpoint half of the generator-membership test. -/
theorem FirstDead.mem_subring_of_endpoint_isUnit (h : D.FirstDead) (A : Subring K)
    (hπ : (D.uniformizer : K) ∈ A)
    (hy : ∀ n, (D.ratio n : K) ∈ A)
    (hz : (D.endpoint h.length : K) ∈ A)
    (hu : IsUnit (⟨D.endpoint h.length, hz⟩ : A)) : h.value ∈ A := by
  have hn : (D.uniformizer : K) ^ h.coefficientExponent *
      ∏ i : Fin h.length, (D.ratio i.val : K) ^ h.powers i ∈ A :=
    A.mul_mem (A.pow_mem hπ _) (A.prod_mem fun i _ => A.pow_mem (hy _) _)
  have hi : (D.endpoint h.length : K)⁻¹ ∈ A :=
    Submonoid.inv_mem_of_isUnit hu
  have heq : h.value = ((D.uniformizer : K) ^ h.coefficientExponent *
      ∏ i : Fin h.length, (D.ratio i.val : K) ^ h.powers i) *
        (D.endpoint h.length : K)⁻¹ := by
    rw [← h.value_mul_endpoint D]
    rw [mul_assoc, mul_inv_cancel₀ (Subtype.coe_ne_coe.mpr (D.endpoint_ne_zero _)), mul_one]
  rw [heq]
  exact A.mul_mem hn hi

/-- Only the nonunit-endpoint prefix requires power returns. -/
theorem FirstDead.mem_subring_of_initial_segment (h : D.FirstDead) (A : Subring K)
    (hπ : (D.uniformizer : K) ∈ A)
    (hy : ∀ n, (D.ratio n : K) ∈ A)
    (hz : (D.endpoint h.length : K) ∈ A)
    (hreturn : ¬ IsUnit (⟨D.endpoint h.length, hz⟩ : A) →
      ∀ i < h.length, (D.ratio i : K) ^ D.returnExponent i /
        (D.uniformizer : K) ^ D.exponent ∈ A) : h.value ∈ A := by
  by_cases hu : IsUnit (⟨D.endpoint h.length, hz⟩ : A)
  · exact h.mem_subring_of_endpoint_isUnit D A hπ hy hz hu
  · exact D.large_monomial_mem_subring_prefix A hπ h.length h.coefficientExponent
      (fun i => h.powers i + 1) (fun i => hy i.val)
      (fun i => hreturn hu i.val i.isLt) h.large

/-- Actual generator containment at one place from initial-segment returns. -/
theorem sourceRing_le_of_initial_segment (O A : Subring K) (hOA : O ≤ A)
    (hπ : (D.uniformizer : K) ∈ O)
    (hz : ∀ n, (D.endpoint n : K) ∈ A)
    (hy : ∀ n, (D.ratio n : K) ∈ A)
    (hreturn : ∀ l, ¬ IsUnit (⟨D.endpoint l, hz l⟩ : A) →
      ∀ i < l, (D.ratio i : K) ^ D.returnExponent i /
        (D.uniformizer : K) ^ D.exponent ∈ A) : D.sourceRing O ≤ A := by
  exact sourceGeneratorRing_le O A _ _ _ hOA hz hy
    (by rintro x ⟨h, rfl⟩
        exact h.mem_subring_of_initial_segment D A (hOA hπ) hy (hz h.length)
          (hreturn h.length))

/-- The family intersection is proved generatorwise, without a premise
asserting the desired containment or globally returning every block power. -/
theorem sourceRing_le_family_of_initial_segment {ι : Type*}
    (O : Subring K) (A : ι → Subring K) (hOA : ∀ j, O ≤ A j)
    (hπ : (D.uniformizer : K) ∈ O)
    (hz : ∀ j n, (D.endpoint n : K) ∈ A j)
    (hy : ∀ j n, (D.ratio n : K) ∈ A j)
    (hreturn : ∀ j l, ¬ IsUnit (⟨D.endpoint l, hz j l⟩ : A j) →
      ∀ i < l, (D.ratio i : K) ^ D.returnExponent i /
        (D.uniformizer : K) ^ D.exponent ∈ A j) :
    D.sourceRing O ≤ ⨅ j, A j := by
  exact le_iInf fun j => D.sourceRing_le_of_initial_segment O (A j) (hOA j) hπ
    (hz j) (hy j) (hreturn j)

end SourceBlockData
end HereditaryAtomicity.DVRBase
