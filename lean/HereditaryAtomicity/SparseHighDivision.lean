import HereditaryAtomicity.SparseConductorBase
import Mathlib.RingTheory.Ideal.Operations

/-!
# Fresh simultaneous division of high relevant generators

A finite family uses only finitely many Laurent coordinates. Its finite-valued
profiles have a uniform positive excess over the cutoff, so an unused generator
with sufficiently small geometric budget divides the whole family.
-/

open scoped NNReal
noncomputable section
namespace HereditaryAtomicity

namespace SparseLaurentKey

def divideVariable (w : SparseLaurentKey) (n : ℕ) : SparseLaurentKey :=
  (w.1 - Finsupp.single n 1,w.2.1,w.2.2)

theorem divideVariable_add (w : SparseLaurentKey) (n : ℕ) :
    divideVariable w n + variableKey n = w := by
  ext j <;> simp [divideVariable,variableKey]

theorem Relevant.divideVariable {w : SparseLaurentKey} (hw : w.Relevant)
    (n : ℕ) (hn : w.1 n = 0) : (w.divideVariable n).Relevant := by
  refine ⟨hw.1,?_⟩
  intro j
  by_cases hj : n=j
  · subst j
    simp [SparseLaurentKey.divideVariable,hn]
  · simpa [SparseLaurentKey.divideVariable,Finsupp.single_eq_of_ne (Ne.symm hj)] using hw.2 j

end SparseLaurentKey

variable {K : Type*} [Field K]

theorem sparseLaurentMonomial_divideVariable (a : ℕ → Kˣ) (x y : Kˣ)
    (w : SparseLaurentKey) (n : ℕ) :
    sparseLaurentMonomial a x y (.ofAdd (w.divideVariable n)) =
      sparseLaurentMonomial a x y (.ofAdd w) / (a n : K) := by
  apply (eq_div_iff (Units.ne_zero (a n))).mpr
  rw [← sparseLaurentMonomial_variable a x y n,← map_mul]
  exact congrArg (sparseLaurentMonomial a x y)
    (congrArg Multiplicative.ofAdd (w.divideVariable_add n))

/-- A finite set of values strictly above a cutoff has one positive uniform gap.
This includes the empty range, so no nonemptiness hypothesis is needed. -/
theorem finite_values_uniform_gap {s : Set ℝ} (hs : s.Finite) (c : ℝ)
    (hc : ∀ z∈s, c<z) : ∃ ε:ℝ, 0<ε ∧ ∀ z∈s, c+ε≤z := by
  induction s, hs using Set.Finite.induction_on with
  | empty => exact ⟨1,by norm_num,by simp⟩
  | @insert z s hz hs ih =>
    obtain ⟨ε,hε,hgap⟩ := ih (fun q hq => hc q (Set.mem_insert_of_mem _ hq))
    refine ⟨min (z-c) ε,lt_min (sub_pos.mpr (hc z (Set.mem_insert _ _))) hε,?_⟩
    intro q hq
    rcases hq with rfl | hq
    · linarith [min_le_left (q-c) ε]
    · linarith [min_le_right (z-c) ε,hgap q hq]

/-- Finite many finite-range profiles have a common positive gap. -/
theorem finite_profiles_uniform_gap {ι α : Type*} (f : α → ι → ℝ)
    (s : Finset α) (c : ℝ)
    (hfinite : ∀ z∈s, Set.Finite (Set.range (f z)))
    (hhigh : ∀ z∈s, ∀ i, c<f z i) :
    ∃ ε:ℝ, 0<ε ∧ ∀ z∈s, ∀ i, c+ε≤f z i := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1,by norm_num,by simp⟩
  | @insert z s hz ih =>
    obtain ⟨δ,hδ,hzGap⟩ := finite_values_uniform_gap
      (hfinite z (Finset.mem_insert_self _ _)) c (by
        rintro _ ⟨i,rfl⟩
        exact hhigh z (Finset.mem_insert_self _ _) i)
    obtain ⟨ε,hε,hgap⟩ := ih
      (fun q hq => hfinite q (Finset.mem_insert_of_mem hq))
      (fun q hq => hhigh q (Finset.mem_insert_of_mem hq))
    refine ⟨min δ ε,lt_min hδ hε,?_⟩
    intro q hq i
    rcases Finset.mem_insert.mp hq with rfl | hq
    · linarith [min_le_left δ ε,hzGap (f q i) ⟨i,rfl⟩]
    · linarith [min_le_right δ ε,hgap q hq i]

/-- A single fresh source generator divides every member of a given finite
family of actual high generators, preserving the high-generator conditions. -/
theorem sparseHighGenerators_finite_division {ι : Type*}
    (v : ι → Valuation K ℝ≥0) (a : ℕ → Kˣ) (x y : Kˣ)
    (π : K) (hπ : π≠0) (c : ℝ)
    (hfinite : ∀ z:K, z≠0 → Set.Finite (Set.range (fun i => realValuationOrder (v i) z)))
    (hbudget : ∀ n i, realValuationOrder (v i) (a n) ≤ sparseProfileBudget n)
    (s : Finset K) (hs : (s:Set K) ⊆ sparseHighGenerators v a x y π c) :
    ∃ n:ℕ, ∀ z∈s, z/(a n:K) ∈ sparseHighGenerators v a x y π c := by
  classical
  have hz0 : ∀ z∈s, z≠0 := by
    intro z hz
    obtain ⟨r,w,_,rfl,_⟩ := hs hz
    exact mul_ne_zero (pow_ne_zero _ hπ) (sparseLaurentMonomial_ne_zero a x y w)
  obtain ⟨ε,hε,hgap⟩ := finite_profiles_uniform_gap
    (fun z i => realValuationOrder (v i) z) s c
    (fun z hz => hfinite z (hz0 z hz))
    (fun z hz => (hs hz).choose_spec.choose_spec.2.2)
  have hreps : ∀ z:s, ∃ r:ℕ, ∃ w:SparseLaurentKey, w.Relevant ∧
      (z:K)=π^r*sparseLaurentMonomial a x y (.ofAdd w) := by
    intro z
    obtain ⟨r,w,hw,hz,_⟩ := hs z.property
    exact ⟨r,w,hw,hz⟩
  choose r w hw hz using hreps
  let supports : Finset ℕ := Finset.univ.biUnion (fun z:s => (w z).1.support)
  obtain ⟨n,hn,hsmall⟩ := exists_sparseProfileBudget_lt (supports.sup id) ε hε
  refine ⟨n,?_⟩
  intro z hzs
  let z' : s := ⟨z,hzs⟩
  have hnFresh : (w z').1 n=0 := by
    by_contra hne
    have hnMem : n∈supports := Finset.mem_biUnion.mpr
      ⟨z',Finset.mem_univ _,Finsupp.mem_support_iff.mpr hne⟩
    have := Finset.le_sup (f:=id) hnMem
    exact (not_le_of_gt hn) this
  refine ⟨r z',(w z').divideVariable n,(hw z').divideVariable n hnFresh,?_,?_⟩
  · rw [sparseLaurentMonomial_divideVariable,← mul_div_assoc,← hz z']
  · intro i
    rw [realValuationOrder_div (v i) (hz0 z hzs) (Units.ne_zero (a n))]
    linarith [hbudget n i,hgap z hzs i]

/-- Finite simultaneous division on generators extends to the whole ideal
span, because membership uses only finitely many generators. -/
theorem span_finite_division {R : Type*} [CommRing R] (G : Set R) (a : ℕ → R)
    (hdiv : ∀ s:Finset R, (s:Set R)⊆G → ∃ n:ℕ, ∀ g∈s, ∃ h∈G, a n*h=g)
    {z:R} (hz : z∈Ideal.span G) :
    ∃ n:ℕ, ∃ q∈Ideal.span G, a n*q=z := by
  obtain ⟨s,hs,hzs⟩ := Submodule.mem_span_finite_of_mem_span hz
  obtain ⟨n,hn⟩ := hdiv s hs
  have hle : Ideal.span (s:Set R) ≤ Ideal.span {a n} * Ideal.span G := by
    apply Ideal.span_le.mpr
    intro g hg
    obtain ⟨q,hq,hqg⟩ := hn g hg
    exact Ideal.mem_span_singleton_mul.mpr ⟨q,Ideal.subset_span hq,hqg⟩
  obtain ⟨q,hq,hqz⟩ := Ideal.mem_span_singleton_mul.mp (hle hzs)
  exact ⟨n,q,hq,hqz⟩

/-- A proper ideal admitting division by prescribed nonunits contains no atoms. -/
theorem span_not_irreducible_of_finite_division {R : Type*} [CommRing R]
    (G : Set R) (a : ℕ → R)
    (hdiv : ∀ s:Finset R, (s:Set R)⊆G → ∃ n:ℕ, ∀ g∈s, ∃ h∈G, a n*h=g)
    (ha : ∀ n, ¬ IsUnit (a n)) (hproper : Ideal.span G≠⊤)
    {z:R} (hz : z∈Ideal.span G) : ¬ Irreducible z := by
  intro hirr
  obtain ⟨n,q,hq,hqz⟩ := span_finite_division G a hdiv hz
  rcases hirr.isUnit_or_isUnit hqz.symm with h | h
  · exact ha n h
  · exact hproper ((Ideal.span G).eq_top_of_isUnit_mem hq h)

/-- The actual ideal generated by all high relevant monomials in a source ring. -/
def sparseHighIdeal {ι : Type*} (v : ι → Valuation K ℝ≥0) (S : Subring K)
    (a : ℕ → Kˣ) (x y : Kˣ) (π : K) (c : ℝ) : Ideal S :=
  Ideal.span {z:S | (z:K)∈sparseHighGenerators v a x y π c}

theorem sparseHighIdeal_le_tail {ι : Type*} (v : ι → Valuation K ℝ≥0)
    (S : Subring K) (hS : ∀ z:S, z≠0 → ∀ i, 0≤realValuationOrder (v i) z)
    (a : ℕ → Kˣ) (x y : Kˣ) (π : K) (c : ℝ) :
    sparseHighIdeal v S a x y π c ≤ realValuationTail v S hS c := by
  apply Ideal.span_le.mpr
  rintro z ⟨r,w,hw,hz,hhigh⟩
  exact Or.inr hhigh

theorem sparseHighIdeal_high {ι : Type*} (v : ι → Valuation K ℝ≥0)
    (S : Subring K) (hS : ∀ z:S, z≠0 → ∀ i, 0≤realValuationOrder (v i) z)
    (a : ℕ → Kˣ) (x y : Kˣ) (π : K) (c : ℝ)
    {z:S} (hz : z∈sparseHighIdeal v S a x y π c) (hz0 : z≠0) :
    ∀ i, c<realValuationOrder (v i) z :=
  (sparseHighIdeal_le_tail v S hS a x y π c hz).resolve_left hz0

/-- Fresh division remains inside the generated ideal of any source containing
all high generators and all selected small generators. -/
theorem sparseHighIdeal_division {ι : Type*}
    (v : ι → Valuation K ℝ≥0) (S : Subring K)
    (a : ℕ → Kˣ) (ha : ∀ n, (a n:K)∈S) (x y : Kˣ)
    (π : K) (hπ : π≠0) (c : ℝ)
    (hG : sparseHighGenerators v a x y π c ⊆ S)
    (hfinite : ∀ z:K, z≠0 → Set.Finite (Set.range (fun i => realValuationOrder (v i) z)))
    (hbudget : ∀ n i, realValuationOrder (v i) (a n) ≤ sparseProfileBudget n)
    {z:S} (hz : z∈sparseHighIdeal v S a x y π c) :
    ∃ n:ℕ, ∃ q∈sparseHighIdeal v S a x y π c, (⟨a n,ha n⟩:S)*q=z := by
  classical
  apply span_finite_division _ (fun n => (⟨a n,ha n⟩:S)) _ hz
  intro s hs
  obtain ⟨n,hn⟩ := sparseHighGenerators_finite_division v a x y π hπ c hfinite hbudget
    (s.image (fun z:S => (z:K))) (by
      rintro t ht
      obtain ⟨g,hg,rfl⟩ := Finset.mem_image.mp ht
      exact hs hg)
  refine ⟨n,?_⟩
  intro g hg
  have hquot := hn (g:K) (Finset.mem_image.mpr ⟨g,hg,rfl⟩)
  refine ⟨⟨(g:K)/(a n:K),hG hquot⟩,hquot,?_⟩
  apply Subtype.ext
  exact mul_div_cancel₀ (g:K) (Units.ne_zero (a n))

/-- Every element of the high ideal is intrinsically nonatomic. -/
theorem sparseHighIdeal_not_irreducible {ι : Type*}
    (v : ι → Valuation K ℝ≥0) (i₀ : ι) (S : Subring K)
    (hS : ∀ z:S, z≠0 → ∀ i, 0≤realValuationOrder (v i) z)
    (a : ℕ → Kˣ) (ha : ∀ n, (a n:K)∈S) (x y : Kˣ)
    (π : K) (hπ : π≠0) (c : ℝ) (hc : 0≤c)
    (hG : sparseHighGenerators v a x y π c ⊆ S)
    (hfinite : ∀ z:K, z≠0 → Set.Finite (Set.range (fun i => realValuationOrder (v i) z)))
    (hbudget : ∀ n i, realValuationOrder (v i) (a n) ≤ sparseProfileBudget n)
    (hpos : ∀ n, 0<realValuationOrder (v i₀) (a n))
    {z:S} (hz : z∈sparseHighIdeal v S a x y π c) : ¬ Irreducible z := by
  intro hirr
  obtain ⟨n,q,hq,hqz⟩ := sparseHighIdeal_division v S a ha x y π hπ c hG hfinite hbudget hz
  rcases hirr.isUnit_or_isUnit hqz.symm with hu | hu
  · exact not_isUnit_of_realValuationOrder_pos (v i₀) S
      (fun z hz => hS z hz i₀) (hpos n) hu
  · have hq0 : q≠0 := by
      intro h
      apply hirr.ne_zero
      rw [← hqz,h,mul_zero]
    have hhigh := sparseHighIdeal_high v S hS a x y π c hq hq0 i₀
    exact not_isUnit_of_realValuationOrder_pos (v i₀) S
      (fun z hz => hS z hz i₀) (hc.trans_lt hhigh) hu

end HereditaryAtomicity
