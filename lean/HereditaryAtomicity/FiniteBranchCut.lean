import HereditaryAtomicity.SparseProductCut
import HereditaryAtomicity.SparseSelection
import Mathlib.Data.Finset.Max
import Mathlib.RingTheory.Localization.FractionRing

/-!
# The concrete finite-branch polynomial cut

The ring is the sum of an actual polynomial evaluation image and an actual
open-tail ideal. Sparse values are used only for the low-term noncancellation
argument; all elements and divisions remain in the given field.
-/

open scoped NNReal BigOperators
noncomputable section
namespace HereditaryAtomicity

variable {K : Type*} [Field K]

/-- The value of a polynomial term in an actual ring. -/
def sparseTerm {R : Type*} [CommRing R] (A : Subring R)
    (a : ℕ → R) (p : MvPolynomial ℕ A) (d : ℕ →₀ ℕ) : R :=
  (p.coeff d : R) * ∏ n ∈ d.support, a n ^ d n

section Polynomial
variable {ι : Type*} (v : ι → Valuation K ℝ≥0) (B : Subring K)
    (hB : ∀ (x : B), x ≠ 0 → ∀ i, 0 ≤ realValuationOrder (v i) x)
    (A : Subring B) (a : ℕ → B) (ha : ∀ n, a n ≠ 0)
    (i₀ : ι) (c : ℝ)
    (hcoeff : ∀ x : A, x ≠ 0 → ∃ r : ℕ, ∀ i, realValuationOrder (v i) ((x : B) : K) = r)
    (hmin : ∀ n i, realValuationOrder (v i₀) (a n) ≤ realValuationOrder (v i) (a n))

include ha in
theorem sparseTerm_ne_zero (p : MvPolynomial ℕ A) {d : ℕ →₀ ℕ} (hd : d ∈ p.support) :
    sparseTerm A a p d ≠ 0 := by
  apply mul_ne_zero
  · exact Subtype.coe_ne_coe.mpr (MvPolynomial.mem_support_iff.mp hd)
  · exact Finset.prod_ne_zero_iff.mpr fun n _ => pow_ne_zero _ (ha n)

include ha in
theorem sparseTerm_order (p : MvPolynomial ℕ A) {d : ℕ →₀ ℕ}
    (hd : d ∈ p.support) (i : ι) :
    realValuationOrder (v i) ((sparseTerm A a p d : B) : K) =
      realValuationOrder (v i) ((p.coeff d : B) : K) +
        sparseWeight (fun n => realValuationOrder (v i) (a n)) d := by
  have hc : ((p.coeff d : B) : K) ≠ 0 := by
    exact Subtype.coe_ne_coe.mpr (Subtype.coe_ne_coe.mpr (MvPolynomial.mem_support_iff.mp hd))
  have hp : (∏ n ∈ d.support, ((a n : B) : K) ^ d n) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun n _ => pow_ne_zero _ (Subtype.coe_ne_coe.mpr (ha n))
  simp only [sparseTerm, Subring.coe_mul, SubmonoidClass.coe_finsetProd, Subring.coe_pow]
  rw [realValuationOrder_mul (v i) hc hp,
    realValuationOrder_prod (v i) d.support (fun n => (a n : K)^d n)
      (fun n _ => pow_ne_zero _ (Subtype.coe_ne_coe.mpr (ha n)))]
  simp only [realValuationOrder_pow, sparseWeight, Finsupp.sum]

include ha hcoeff hmin in
theorem sparseTerm_minimum (p : MvPolynomial ℕ A) {d : ℕ →₀ ℕ}
    (hd : d ∈ p.support) (i : ι) :
    realValuationOrder (v i₀) ((sparseTerm A a p d : B) : K) ≤
      realValuationOrder (v i) ((sparseTerm A a p d : B) : K) := by
  obtain ⟨r, hr⟩ := hcoeff (p.coeff d) (MvPolynomial.mem_support_iff.mp hd)
  rw [sparseTerm_order v B A a ha p hd i₀, sparseTerm_order v B A a ha p hd i,
    hr i₀, hr i]
  apply add_le_add_right
  exact Finset.sum_le_sum fun n _ => mul_le_mul_of_nonneg_left (hmin n i) (Nat.cast_nonneg _)

include ha hcoeff in
theorem sparseTerm_order_in_monoid (M : AddSubmonoid ℝ) (h1 : (1 : ℝ) ∈ M)
    (hγ : ∀ n, realValuationOrder (v i₀) (a n) ∈ M)
    (p : MvPolynomial ℕ A) {d : ℕ →₀ ℕ} (hd : d ∈ p.support) :
    realValuationOrder (v i₀) ((sparseTerm A a p d : B) : K) ∈ M := by
  obtain ⟨r, hr⟩ := hcoeff (p.coeff d) (MvPolynomial.mem_support_iff.mp hd)
  rw [sparseTerm_order v B A a ha p hd i₀, hr i₀]
  apply M.add_mem
  · simpa using M.nsmul_mem h1 r
  · apply M.sum_mem
    intro n _
    simpa [nsmul_eq_mul] using M.nsmul_mem (hγ n) (d n)

include ha hcoeff hmin in
/-- Sparse low values force a unique least polynomial term unless the whole
polynomial belongs to the open tail. -/
theorem sparsePolynomial_tail_or_leading
    (htie : ∀ (r s : ℕ) (d e : ℕ →₀ ℕ),
      (r : ℝ) + sparseWeight (fun n => realValuationOrder (v i₀) (a n)) d ≤ c →
      (s : ℝ) + sparseWeight (fun n => realValuationOrder (v i₀) (a n)) e ≤ c →
      (r : ℝ) + sparseWeight (fun n => realValuationOrder (v i₀) (a n)) d =
        (s : ℝ) + sparseWeight (fun n => realValuationOrder (v i₀) (a n)) e → d=e)
    (p : MvPolynomial ℕ A) :
    p.eval₂ A.subtype a ∈ realValuationTail v B hB c ∨
      ∃ d ∈ p.support,
        realValuationOrder (v i₀) ((sparseTerm A a p d : B) : K) ≤ c ∧
        ((p.eval₂ A.subtype a : B) : K) ≠ 0 ∧
        realValuationOrder (v i₀) ((p.eval₂ A.subtype a : B) : K) =
          realValuationOrder (v i₀) ((sparseTerm A a p d : B) : K) := by
  classical
  by_cases hlow : ∃ d ∈ p.support, realValuationOrder (v i₀) ((sparseTerm A a p d : B) : K) ≤ c
  · obtain ⟨d, hd, hdle⟩ := hlow
    obtain ⟨e, he, hleast⟩ := p.support.exists_min_image
      (fun e => realValuationOrder (v i₀) ((sparseTerm A a p e : B) : K)) ⟨d, hd⟩
    have hele : realValuationOrder (v i₀) ((sparseTerm A a p e : B) : K) ≤ c :=
      (hleast d hd).trans hdle
    have hstrict : ∀ f ∈ p.support, f ≠ e →
        realValuationOrder (v i₀) ((sparseTerm A a p e : B) : K) <
          realValuationOrder (v i₀) ((sparseTerm A a p f : B) : K) := by
      intro f hf hfe
      apply lt_of_le_of_ne (hleast f hf)
      intro hsame
      obtain ⟨r, hr⟩ := hcoeff (p.coeff e) (MvPolynomial.mem_support_iff.mp he)
      obtain ⟨s, hs⟩ := hcoeff (p.coeff f) (MvPolynomial.mem_support_iff.mp hf)
      have hform_e := sparseTerm_order v B A a ha p he i₀
      have hform_f := sparseTerm_order v B A a ha p hf i₀
      rw [hr i₀] at hform_e
      rw [hs i₀] at hform_f
      exact hfe (htie r s e f (hform_e ▸ hele)
        (hform_f ▸ hsame ▸ hele) (hform_e.symm.trans (hsame.trans hform_f))).symm
    have hsum := realValuationOrder_sum_eq_of_unique_min (v i₀) p.support
      (fun d => ((sparseTerm A a p d : B) : K))
      (fun d hd => Subtype.coe_ne_coe.mpr (sparseTerm_ne_zero B A a ha p hd)) he hstrict
    right
    refine ⟨e, he, hele, ?_, ?_⟩
    · simpa only [MvPolynomial.eval₂_eq, sparseTerm, Subring.subtype_apply, AddSubmonoidClass.coe_finsetSum, Subring.coe_mul,
        SubmonoidClass.coe_finsetProd, Subring.coe_pow] using hsum.1
    · simpa only [MvPolynomial.eval₂_eq, sparseTerm, Subring.subtype_apply, AddSubmonoidClass.coe_finsetSum, Subring.coe_mul,
        SubmonoidClass.coe_finsetProd, Subring.coe_pow] using hsum.2
  · left
    rw [MvPolynomial.eval₂_eq]
    apply Submodule.sum_mem
    intro d hd
    right
    intro i
    have hi₀ : c < realValuationOrder (v i₀) ((sparseTerm A a p d : B) : K) :=
      lt_of_not_ge (fun h => hlow ⟨d, hd, h⟩)
    exact hi₀.trans_le (sparseTerm_minimum v B A a ha i₀ hcoeff hmin p hd i)

/-- The literal polynomial evaluation image plus the common open-tail ideal. -/
def polynomialTailRing : Subring B :=
  subringPlusIdeal (MvPolynomial.eval₂Hom A.subtype a).range (realValuationTail v B hB c)

@[simp] theorem mem_polynomialTailRing (x : B) :
    x ∈ polynomialTailRing v B hB A a c ↔
      ∃ p : MvPolynomial ℕ A, ∃ z ∈ realValuationTail v B hB c,
        x = p.eval₂ A.subtype a + z := by
  constructor
  · rintro ⟨y, ⟨p, rfl⟩, z, hz, rfl⟩
    exact ⟨p, z, hz, rfl⟩
  · rintro ⟨p, z, hz, rfl⟩
    exact ⟨p.eval₂ A.subtype a, ⟨p, rfl⟩, z, hz, rfl⟩

theorem variable_mem_polynomialTailRing (n : ℕ) :
    a n ∈ polynomialTailRing v B hB A a c := by
  apply (mem_polynomialTailRing v B hB A a c (a n)).mpr
  exact ⟨MvPolynomial.X n, 0, (realValuationTail v B hB c).zero_mem, by simp⟩

theorem tail_subset_polynomialTailRing :
    (realValuationTail v B hB c : Set B) ⊆ polynomialTailRing v B hB A a c :=
  ideal_subset_subringPlusIdeal _ _

include ha hcoeff hmin in
theorem polynomialTailRing_order_mem
    (htie : ∀ (r s : ℕ) (d e : ℕ →₀ ℕ),
      (r : ℝ) + sparseWeight (fun n => realValuationOrder (v i₀) (a n)) d ≤ c →
      (s : ℝ) + sparseWeight (fun n => realValuationOrder (v i₀) (a n)) e ≤ c →
      (r : ℝ) + sparseWeight (fun n => realValuationOrder (v i₀) (a n)) d =
        (s : ℝ) + sparseWeight (fun n => realValuationOrder (v i₀) (a n)) e → d=e)
    (M : AddSubmonoid ℝ) (h1 : (1 : ℝ) ∈ M)
    (hγ : ∀ n, realValuationOrder (v i₀) (a n) ∈ M)
    {x : B} (hx : x ∈ polynomialTailRing v B hB A a c)
    (hxI : x ∉ realValuationTail v B hB c) : realValuationOrder (v i₀) x ∈ M := by
  obtain ⟨p, z, hz, rfl⟩ := (mem_polynomialTailRing v B hB A a c x).mp hx
  rcases sparsePolynomial_tail_or_leading v B hB A a ha i₀ c hcoeff hmin htie p with hp | hp
  · exact (hxI ((realValuationTail v B hB c).add_mem hp hz)).elim
  obtain ⟨d, hd, hdle, hp0, hpval⟩ := hp
  have hpmem : realValuationOrder (v i₀) ((p.eval₂ A.subtype a : B) : K) ∈ M := by
    rw [hpval]
    exact sparseTerm_order_in_monoid v B A a ha i₀ hcoeff M h1 hγ p hd
  rcases hz with rfl | hz
  · simpa using hpmem
  by_cases hz0 : z = 0
  · simpa [hz0] using hpmem
  have hlt : realValuationOrder (v i₀) ((p.eval₂ A.subtype a : B) : K) <
      realValuationOrder (v i₀) (z : K) := (hpval ▸ hdle).trans_lt (hz i₀)
  have hval := (realValuationOrder_add_eq_min (v i₀) hp0
    (Subtype.coe_ne_coe.mpr hz0) (ne_of_lt hlt)).2
  rw [min_eq_left hlt.le] at hval
  change realValuationOrder (v i₀) (((p.eval₂ A.subtype a : B) : K)+(z : K)) ∈ M
  exact hval ▸ hpmem

include ha i₀ in
/-- Every nonzero tail element splits into two intrinsic nonunits, using an
actual source generator smaller than its excess above the cutoff at every branch. -/
theorem polynomialTailRing_tail_not_irreducible [Finite ι]
    (hc : 0 ≤ c)
    (hBmem : ∀ x : K, (∀ i, v i x ≤ 1) → x ∈ B)
    (hpos : ∀ n i, 0 < realValuationOrder (v i) (a n))
    (hsmall : ∀ ε : ℝ, 0 < ε → ∃ n, ∀ i, realValuationOrder (v i) (a n) < ε)
    (y : polynomialTailRing v B hB A a c)
    (hy : (y : B) ∈ realValuationTail v B hB c) : ¬ Irreducible y := by
  classical
  intro hirr
  have hy0 : (y : B) ≠ 0 := Subtype.coe_ne_coe.mpr hirr.ne_zero
  have hyK : ((y : B) : K) ≠ 0 := Subtype.coe_ne_coe.mpr hy0
  have hyval : ∀ i, c < realValuationOrder (v i) ((y : B) : K) :=
    hy.resolve_left hy0
  let : Fintype ι := Fintype.ofFinite ι
  obtain ⟨j, _, hj⟩ := Finset.univ.exists_min_image
    (fun i => realValuationOrder (v i) ((y : B) : K) - c) ⟨i₀, Finset.mem_univ _⟩
  obtain ⟨n, hn⟩ := hsmall (realValuationOrder (v j) ((y : B) : K)-c)
    (sub_pos.mpr (hyval j))
  have hgap : ∀ i, realValuationOrder (v i) (a n) <
      realValuationOrder (v i) ((y : B) : K)-c := fun i =>
    (hn i).trans_le (hj i (Finset.mem_univ _))
  let q : K := ((y : B) : K) / (a n : K)
  have hq0 : q ≠ 0 := div_ne_zero hyK (Subtype.coe_ne_coe.mpr (ha n))
  have hqval : ∀ i, c < realValuationOrder (v i) q := by
    intro i
    dsimp only [q]
    rw [realValuationOrder_div (v i) hyK (Subtype.coe_ne_coe.mpr (ha n))]
    linarith [hgap i]
  have hqB : q ∈ B := hBmem q fun i =>
    (realValuationOrder_nonneg_iff (v i) hq0).mp (hc.trans (hqval i).le)
  let qB : B := ⟨q, hqB⟩
  have hqI : qB ∈ realValuationTail v B hB c := Or.inr hqval
  let xS : polynomialTailRing v B hB A a c :=
    ⟨a n, variable_mem_polynomialTailRing v B hB A a c n⟩
  let qS : polynomialTailRing v B hB A a c :=
    ⟨qB, tail_subset_polynomialTailRing v B hB A a c hqI⟩
  have hfac : y = xS*qS := by
    apply Subtype.ext
    apply Subtype.ext
    exact (mul_div_cancel₀ ((y : B) : K) (Subtype.coe_ne_coe.mpr (ha n))).symm
  rcases hirr.isUnit_or_isUnit hfac with hx | hq
  · have hu := hx.map (polynomialTailRing v B hB A a c).subtype
    exact not_isUnit_of_realValuationOrder_pos (v i₀) B (fun x hx => hB x hx i₀)
      (hpos n i₀) hu
  · have hu := hq.map (polynomialTailRing v B hB A a c).subtype
    exact not_isUnit_of_realValuationOrder_pos (v i₀) B (fun x hx => hB x hx i₀)
      (hc.trans_lt (hqval i₀)) hu

include ha hcoeff hmin in
/-- The actual polynomial-plus-tail subring is nonatomic when its selected
endpoint order is excluded from the sparse additive monoid. -/
theorem not_isAtomicDomain_polynomialTailRing [Finite ι]
    (hc : 0 ≤ c)
    (hBmem : ∀ x : K, (∀ i, v i x ≤ 1) → x ∈ B)
    (hpos : ∀ n i, 0 < realValuationOrder (v i) (a n))
    (hsmall : ∀ ε : ℝ, 0 < ε → ∃ n, ∀ i, realValuationOrder (v i) (a n) < ε)
    (htie : ∀ (r s : ℕ) (d e : ℕ →₀ ℕ),
      (r : ℝ) + sparseWeight (fun n => realValuationOrder (v i₀) (a n)) d ≤ c →
      (s : ℝ) + sparseWeight (fun n => realValuationOrder (v i₀) (a n)) e ≤ c →
      (r : ℝ) + sparseWeight (fun n => realValuationOrder (v i₀) (a n)) d =
        (s : ℝ) + sparseWeight (fun n => realValuationOrder (v i₀) (a n)) e → d=e)
    (M : AddSubmonoid ℝ) (h1 : (1 : ℝ) ∈ M)
    (hγ : ∀ n, realValuationOrder (v i₀) (a n) ∈ M)
    (x : B) (hx0 : x ≠ 0) (hxI : x ∈ realValuationTail v B hB c)
    (hxM : realValuationOrder (v i₀) x ∉ M) :
    ¬ Factorization.IsAtomicDomain (polynomialTailRing v B hB A a c) := by
  let S := polynomialTailRing v B hB A a c
  let o : S → ℝ := fun y => realValuationOrder (v i₀) ((y : B) : K)
  let xS : S := ⟨x, tail_subset_polynomialTailRing v B hB A a c hxI⟩
  apply not_isAtomicDomain_of_atomOrders o M (by simp [o]) _ _ _ xS
    (by intro h; exact hx0 (congrArg Subtype.val h)) hxM
  · intro y z hy hz
    exact realValuationOrder_mul (v i₀)
      (Subtype.coe_ne_coe.mpr (Subtype.coe_ne_coe.mpr hy))
      (Subtype.coe_ne_coe.mpr (Subtype.coe_ne_coe.mpr hz))
  · intro y hy
    exact realValuationOrder_eq_zero_of_isUnit (v i₀) B (fun z hz => hB z hz i₀)
      (hy.map S.subtype)
  · intro y hy
    apply polynomialTailRing_order_mem v B hB A a ha i₀ c hcoeff hmin htie M h1 hγ y.property
    intro hyI
    exact polynomialTailRing_tail_not_irreducible v B hB A a ha i₀ c hc hBmem hpos hsmall y hyI hy

theorem polynomialTailRing_le (C : Subring B) (hAC : A ≤ C) (haC : ∀ n, a n ∈ C)
    (hIC : (realValuationTail v B hB c : Set B) ⊆ C) :
    polynomialTailRing v B hB A a c ≤ C := by
  intro x hx
  obtain ⟨p, z, hz, rfl⟩ := (mem_polynomialTailRing v B hB A a c x).mp hx
  apply C.add_mem _ (hIC hz)
  rw [MvPolynomial.eval₂_eq]
  apply C.sum_mem
  intro d _
  apply C.mul_mem (hAC (p.coeff d).property)
  apply C.prod_mem
  intro n _
  exact C.pow_mem (haC n) _

end Polynomial

/-- Simultaneously coinitial actual source elements produce a literal nonatomic
subring containing a nonzero common open-tail ideal. The normalization branches
may have arbitrary real values. -/
theorem exists_nonatomic_polynomial_tail
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (v : ι → Valuation K ℝ≥0) (B : Subring K)
    (hB : ∀ (x : B), x ≠ 0 → ∀ i, 0 ≤ realValuationOrder (v i) x)
    (hBmem : ∀ x : K, (∀ i, v i x ≤ 1) → x ∈ B)
    (C : Subring B) (A : Subring B) (hAC : A ≤ C)
    (hcoeff : ∀ x : A, x ≠ 0 → ∃ r : ℕ, ∀ i,
      realValuationOrder (v i) ((x : B) : K) = r)
    (π : B) (hπ : π ≠ 0) (hπval : ∀ i, realValuationOrder (v i) π = 1)
    (c : ℕ) (hc : 0 < c)
    (hIC : (realValuationTail v B hB c : Set B) ⊆ C)
    (hsmall : ∀ ε : ℝ, 0 < ε → ∃ x : B, x ∈ C ∧ x ≠ 0 ∧
      ∀ i, 0 < realValuationOrder (v i) x ∧ realValuationOrder (v i) x < ε) :
    ∃ S : Subring B, S ≤ C ∧ ¬ Factorization.IsAtomicDomain S ∧
      (realValuationTail v B hB c : Set B) ⊆ S ∧
      realValuationTail v B hB c ≠ ⊥ := by
  classical
  let CK : Subring K := C.map B.subtype
  let ν : ι → K → ℝ := fun i => realValuationOrder (v i)
  have hsmallK : ∀ ε : ℝ, 0 < ε → ∃ x : K, x ∈ CK ∧ x ≠ 0 ∧
      ∀ i, 0 < ν i x ∧ ν i x < ε := by
    intro ε hε
    obtain ⟨x, hxC, hx0, hx⟩ := hsmall ε hε
    exact ⟨x, ⟨x, hxC, rfl⟩, Subtype.coe_ne_coe.mpr hx0, hx⟩
  obtain ⟨i₀, hfixed⟩ := exists_coinitial_minimum_branch CK ν hsmallK
  obtain ⟨b, hbC, hb0, hb⟩ := hfixed 1 zero_lt_one
  have hbB : b ∈ B := by
    obtain ⟨x, _, rfl⟩ := hbC
    exact x.property
  let x : B := π^c * ⟨b, hbB⟩
  have hx0 : x ≠ 0 := mul_ne_zero (pow_ne_zero c hπ) (by
    intro h
    exact hb0 (congrArg Subtype.val h))
  have hxval : ∀ i, realValuationOrder (v i) x = (c : ℝ) + ν i b := by
    intro i
    change realValuationOrder (v i) ((π : K)^c*b) = _
    rw [realValuationOrder_mul (v i) (pow_ne_zero _ (Subtype.coe_ne_coe.mpr hπ)) hb0,
      realValuationOrder_pow, hπval i, mul_one]
  have hxI : x ∈ realValuationTail v B hB c := by
    right
    intro i
    rw [hxval i]
    linarith [(hb i).1]
  let β : ℝ := realValuationOrder (v i₀) x
  have hβ : ∀ r : ℕ, (r : ℝ) ≠ β := by
    intro r heq
    have hrlo : (c : ℝ) < r := by rw [heq]; dsimp only [β]; rw [hxval i₀]; linarith [(hb i₀).1]
    have hrhi : (r : ℝ) < c+1 := by rw [heq]; dsimp only [β]; rw [hxval i₀]; linarith [(hb i₀).2.1]
    have hrlo' : c < r := by exact_mod_cast hrlo
    have hrhi' : r < c+1 := by exact_mod_cast hrhi
    omega
  obtain ⟨aK, haK, htie, havoid⟩ := exists_sparse_source_sequence CK ν i₀
    (fun i x y hx hy => realValuationOrder_mul (v i) hx hy) hfixed c β hβ
  have haKB (n : ℕ) : aK n ∈ B := by
    obtain ⟨x, _, hx⟩ := (haK n).1
    rw [← hx]
    exact x.property
  let a : ℕ → B := fun n => ⟨aK n, haKB n⟩
  have haC : ∀ n, a n ∈ C := by
    intro n
    obtain ⟨x, hxC, hx⟩ := (haK n).1
    have heq : a n = x := Subtype.ext hx.symm
    exact heq ▸ hxC
  have ha0 : ∀ n, a n ≠ 0 := by
    intro n h
    exact (haK n).2.1 (congrArg Subtype.val h)
  have hapos : ∀ n i, 0 < realValuationOrder (v i) (a n) := fun n i => (haK n).2.2 i |>.1
  have hamin : ∀ n i, realValuationOrder (v i₀) (a n) ≤ realValuationOrder (v i) (a n) :=
    fun n i => (haK n).2.2 i |>.2.2
  have hasmall : ∀ ε : ℝ, 0 < ε → ∃ n, ∀ i,
      realValuationOrder (v i) (a n) < ε := by
    intro ε hε
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
    exact ⟨n, fun i => ((haK n).2.2 i).2.1.trans hn⟩
  let M := sparseValueMonoid (fun n => ν i₀ (aK n))
  have hxM : realValuationOrder (v i₀) x ∉ M := by
    rintro ⟨r, d, heq⟩
    exact havoid r d heq.symm
  let S := polynomialTailRing v B hB A a c
  refine ⟨S, polynomialTailRing_le v B hB A a c C hAC haC hIC, ?_,
    tail_subset_polynomialTailRing v B hB A a c, ?_⟩
  · exact not_isAtomicDomain_polynomialTailRing v B hB A a ha0 i₀ c hcoeff hamin
      (le_of_lt (Nat.cast_pos.mpr hc)) hBmem hapos hasmall (fun r s d e hd he heq => (htie r s d e hd he heq).2)
      M (one_mem_sparseValueMonoid _) (generator_mem_sparseValueMonoid _)
      x hx0 hxI hxM
  · intro hzero
    exact hx0 (Ideal.mem_bot.mp (hzero ▸ hxI))

end HereditaryAtomicity
