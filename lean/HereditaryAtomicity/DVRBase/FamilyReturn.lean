import HereditaryAtomicity.DVRBase.SourceConstruction
import HereditaryAtomicity.DVRBase.SemilocalReduction

/-!
# Source return in families of rings and stalks

The simultaneous membership bound applies Lemma 5.3 using the same numerical data in every
subring of a family, with actual power-return quotients in each ring. The MR
interface returns a quotient through any specified set of maximal stalks;
its denominator must be a unit at all remaining stalks. No finiteness or
hereditary-atomicity assumption is required for these membership assertions.
-/

noncomputable section
namespace HereditaryAtomicity.DVRBase
open scoped BigOperators
variable {K : Type*} [Field K]

namespace SourceBlockData
variable {R : Subring K} (D : SourceBlockData R)

/-- Lemma D in another source subring. The same ratios, return exponents and
valuation weights are retained; their power quotients must return in `A`. -/
theorem large_monomial_mem_subring (A : Subring K)
    (hπ : (D.uniformizer : K) ∈ A)
    (hy : ∀ n, (D.ratio n : K) ∈ A)
    (hreturn : ∀ n,
      (D.ratio n : K) ^ D.returnExponent n / (D.uniformizer : K) ^ D.exponent ∈ A)
    (l e : ℕ) (q : Fin l → ℕ)
    (hlarge : D.threshold l ≤ (e : ℝ) - D.exponent +
      ∑ i : Fin l, (q i : ℝ) * D.weight i.val) :
    (D.uniformizer : K) ^ e / (D.uniformizer : K) ^ D.exponent *
      ∏ i : Fin l, (D.ratio i.val : K) ^ q i ∈ A := by
  let πA : A := ⟨D.uniformizer, hπ⟩
  let yA : Fin l → A := fun i => ⟨D.ratio i.val, hy i.val⟩
  exact large_monomial_mem_source A πA
    (fun h => D.uniformizer_ne_zero (Subtype.ext (congrArg A.subtype h))) yA
    D.exponent e (fun i => D.returnExponent i.val) q (fun i => D.weight i.val)
    (fun i => hreturn i.val) (fun i => (D.ratio_order_pos i.val).le)
    (fun i => (D.weight_lt_exponent i.val).le) hlarge

/-- Simultaneous monomial membership for an arbitrary family of source subrings containing the coefficient
ring. The power-return witnesses are checked separately in every family member. -/
theorem large_monomial_mem_family {ι : Type*} (O : Subring K) (A : ι → Subring K)
    (hOA : ∀ i, O ≤ A i) (hπ : (D.uniformizer : K) ∈ O)
    (hy : ∀ i n, (D.ratio n : K) ∈ A i)
    (hreturn : ∀ i n,
      (D.ratio n : K) ^ D.returnExponent n / (D.uniformizer : K) ^ D.exponent ∈ A i)
    (l e : ℕ) (q : Fin l → ℕ)
    (hlarge : D.threshold l ≤ (e : ℝ) - D.exponent +
      ∑ j : Fin l, (q j : ℝ) * D.weight j.val) :
    ∀ i, (D.uniformizer : K) ^ e / (D.uniformizer : K) ^ D.exponent *
      ∏ j : Fin l, (D.ratio j.val : K) ^ q j ∈ A i := by
  intro i
  exact D.large_monomial_mem_subring (A i) (hOA i hπ) (hy i) (hreturn i) l e q hlarge

/-- All first-dead quotients return to a subring with the same power-return
witnesses. No valuation-containment hypothesis on that subring is used. -/
theorem FirstDead.mem_subring (h : D.FirstDead) (A : Subring K)
    (hπ : (D.uniformizer : K) ∈ A)
    (hy : ∀ n, (D.ratio n : K) ∈ A)
    (hreturn : ∀ n,
      (D.ratio n : K) ^ D.returnExponent n / (D.uniformizer : K) ^ D.exponent ∈ A) :
    h.value ∈ A :=
  D.large_monomial_mem_subring A hπ hy hreturn h.length h.coefficientExponent
    (fun i => h.powers i + 1) h.large

/-- The actual source ring lies in every family member once the endpoints,
ratios and prescribed power-return quotients do. First-dead membership follows
from simultaneous membership and is not an additional premise. -/
theorem sourceRing_le_family {ι : Type*} (O : Subring K) (A : ι → Subring K)
    (hOA : ∀ i, O ≤ A i) (hπ : (D.uniformizer : K) ∈ O)
    (hz : ∀ i n, (D.endpoint n : K) ∈ A i)
    (hy : ∀ i n, (D.ratio n : K) ∈ A i)
    (hreturn : ∀ i n,
      (D.ratio n : K) ^ D.returnExponent n / (D.uniformizer : K) ^ D.exponent ∈ A i) :
    ∀ i, D.sourceRing O ≤ A i := by
  intro i
  exact sourceGeneratorRing_le O (A i) _ _ _ (hOA i) (hz i) (hy i)
    (by rintro x ⟨h, rfl⟩; exact h.mem_subring D (A i) (hOA i hπ) (hy i) (hreturn i))

/-- The same family containment holds for every selected source subring. -/
theorem sourceSubring_le_family {ι : Type*} (O : Subring K) (A : ι → Subring K)
    (hOA : ∀ i, O ≤ A i) (hπ : (D.uniformizer : K) ∈ O)
    (hz : ∀ i n, (D.endpoint n : K) ∈ A i)
    (hy : ∀ i n, (D.ratio n : K) ∈ A i)
    (hreturn : ∀ i n,
      (D.ratio n : K) ^ D.returnExponent n / (D.uniformizer : K) ^ D.exponent ∈ A i)
    (Λ : Set ℕ) : ∀ i, D.sourceSubring O Λ ≤ A i :=
  fun i => (D.sourceSubring_le_sourceRing O Λ).trans
    (D.sourceRing_le_family O A hOA hπ hz hy hreturn i)

end SourceBlockData

/-- MR for a source described as an intersection. Quotient membership is
checked on a set of places, and denominator units handle its complement. -/
theorem div_mem_of_mem_at_set_and_units_elsewhere
    {ι : Type*} (D : Subring K) (R : ι → Subring K)
    (hD : ∀ x : K, x ∈ D ↔ ∀ i, x ∈ R i) (places : Set ι)
    {g y : K} (hg : g ∈ D) (hy : y ∈ D)
    (hchosen : ∀ i ∈ places, g / y ∈ R i)
    (hunits : ∀ i, i ∉ places → IsUnit (⟨y, (hD y).mp hy i⟩ : R i)) :
    g / y ∈ D := by
  classical
  apply (hD _).mpr
  intro i
  by_cases hi : i ∈ places
  · exact hchosen i hi
  · have hinv : y⁻¹ ∈ R i := Submonoid.inv_mem_of_isUnit (hunits i hi)
    simpa only [div_eq_mul_inv] using (R i).mul_mem ((hD g).mp hg i) hinv

/-- Return through several actual maximal stalks. There is no requirement
that the selected set or the full maximal spectrum be finite. -/
theorem source_div_mem_of_stalks_and_units (D : Subring K) [IsFractionRing D K]
    (places : Set (MaximalSpectrum D)) {g : K} (hg : g ∈ D) (y : D)
    (hchosen : ∀ M ∈ places, g / (y : K) ∈ sourceMaximalStalk D M)
    (hunits : ∀ M, M ∉ places → IsUnit (sourceMaximalMap D M y)) :
    g / (y : K) ∈ D :=
  div_mem_of_mem_at_set_and_units_elsewhere D (sourceMaximalStalk D)
    (mem_source_iff_mem_stalks D) places hg y.property hchosen hunits

end HereditaryAtomicity.DVRBase
