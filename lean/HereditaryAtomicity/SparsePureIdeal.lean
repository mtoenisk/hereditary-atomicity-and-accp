import HereditaryAtomicity.SparsePureTerms
import HereditaryAtomicity.SparseHighDivision
import HereditaryAtomicity.ArithmeticDVR

/-! # Pure polynomial terms and the actual high ideal -/
open scoped NNReal
noncomputable section
namespace HereditaryAtomicity
variable {K : Type*} [Field K]

/-- A zero or high collected value has no low collected term, including the
case where its entire evaluation vanishes. -/
theorem sparseLaurent_terms_high_of_zero_or_high {ι : Type*}
    (v : ι → Valuation K ℝ≥0) (R A : Subring K)
    (a : ℕ → Kˣ) (x y : Kˣ) (c : ℝ) (hc : 0≤c)
    (hcoeff : ∀ b:A, b≠0 → ∃ r:ℕ, ∀ i, realValuationOrder (v i) (b:K)=r)
    (hsep : SparseLaurentSeparated v a x y (2*c))
    (p : AddMonoidAlgebra A SparseLaurentKey) (hp : SparseCollected v R A a x y c p)
    (hhigh : sparseLaurentEval A a x y p ∈ realOrderAbove v c) :
    ∀ w∈p.coeff.support, ∀ i, c<realValuationOrder (v i) (sparseLaurentTerm A a x y p w) := by
  intro w hw i
  by_contra h
  have hlo := le_of_not_gt h
  obtain ⟨u,_,hu,hp0,heq⟩ := sparseLaurent_leading v R A a x y c hcoeff hsep p hp i hw
    (hlo.trans (by linarith))
  rcases hhigh with hzero | hh
  · exact hp0 hzero
  · exact (not_lt_of_ge (heq ▸ hu.trans hlo)) (hh i)

/-- Remove the actual coefficient unit to express a high pure term as a
source-unit multiple of an actual high generator. -/
theorem sparsePure_high_term_mem {ι : Type*}
    (v : ι → Valuation K ℝ≥0) (S A : Subring K) [IsDiscreteValuationRing A]
    (hAS : A≤S) (hS : ∀ z:S, z≠0 → ∀ i, 0≤realValuationOrder (v i) z)
    (a : ℕ → Kˣ) (x y : Kˣ) (π:A) (hπ:Irreducible π) (c:ℝ)
    (hG : sparseHighGenerators v a x y π c ⊆ S)
    (p : AddMonoidAlgebra A SparseLaurentKey) (hp : SparsePure p)
    (w : SparseLaurentKey) (hw:w∈p.coeff.support)
    (ht : ∀ i,c<realValuationOrder (v i) (sparseLaurentTerm A a x y p w))
    (hmem : sparseLaurentTerm A a x y p w∈S) :
    (⟨sparseLaurentTerm A a x y p w,hmem⟩:S)∈sparseHighIdeal v S a x y π c := by
  obtain ⟨r,u,hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
    (Finsupp.mem_support_iff.mp hw) hπ
  let uS : S := Subring.inclusion hAS u
  have huS : IsUnit uS := u.isUnit.map (Subring.inclusion hAS)
  let g : K := (π:K)^r*sparseLaurentMonomial a x y (.ofAdd w)
  have hg0 : g≠0 := mul_ne_zero (pow_ne_zero _ (Subtype.coe_ne_coe.mpr hπ.ne_zero))
    (sparseLaurentMonomial_ne_zero a x y w)
  have heq : sparseLaurentTerm A a x y p w=(uS:K)*g := by
    simp only [sparseLaurentTerm,hu,Subring.coe_mul,Subring.coe_pow]
    change ((u:A):K)*(π:K)^r*_ = ((u:A):K)*((π:K)^r*_)
    ring
  have hg : g∈sparseHighGenerators v a x y π c := by
    refine ⟨r,w,(hp w (Finsupp.mem_support_iff.mp hw)).relevant,rfl,?_⟩
    intro i
    have ho := ht i
    rw [heq,realValuationOrder_mul (v i) (Subtype.coe_ne_coe.mpr huS.ne_zero) hg0,
      realValuationOrder_eq_zero_of_isUnit (v i) S (fun z hz => hS z hz i) huS,
      zero_add] at ho
    exact ho
  have hm : (⟨g,hG hg⟩:S)∈sparseHighIdeal v S a x y π c := Ideal.subset_span hg
  convert (sparseHighIdeal v S a x y π c).mul_mem_left uS hm using 1
  apply Subtype.ext
  exact heq

/-- A pure polynomial whose evaluation is zero or uniformly high belongs to
this actual high ideal; no low-term cancellation is assumed. -/
theorem sparsePure_eval_mem_highIdeal {ι : Type*}
    (v : ι → Valuation K ℝ≥0) (S A : Subring K) [IsDiscreteValuationRing A]
    (hAS:A≤S) (hS:∀z:S,z≠0→∀i,0≤realValuationOrder (v i) z)
    (a:ℕ→Kˣ) (ha:∀n,(a n:K)∈S) (x y:Kˣ) (π:A) (hπ:Irreducible π)
    (c:ℝ) (hc:0≤c) (hG:sparseHighGenerators v a x y π c⊆S)
    (hcoeff:∀b:A,b≠0→∃r:ℕ,∀i,realValuationOrder (v i) (b:K)=r)
    (hsep:SparseLaurentSeparated v a x y (2*c))
    (p:AddMonoidAlgebra A SparseLaurentKey) (hp:p∈sparsePurePolynomialRing A)
    (hhigh:sparseLaurentEval A a x y p∈realOrderAbove v c) :
    (⟨sparseLaurentEval A a x y p,sparsePurePolynomialRing_eval_mem S A hAS a ha x y hp⟩:S)
      ∈sparseHighIdeal v S a x y π c := by
  classical
  have hcol := sparsePurePolynomialRing_collected v S A hAS
    (fun z hz hz0 => hS ⟨z,hz⟩ (Subtype.coe_ne_coe.mp hz0)) a ha x y c hp
  have hterms := sparseLaurent_terms_high_of_zero_or_high v S A a x y c hc hcoeff hsep p hcol hhigh
  let f : SparseLaurentKey → S := fun w => ⟨sparseLaurentTerm A a x y p w,(hcol w).1⟩
  have hsum : (∑ w∈p.coeff.support,f w)∈sparseHighIdeal v S a x y π c := by
    apply Ideal.sum_mem
    intro w hw
    exact sparsePure_high_term_mem v S A hAS hS a x y π hπ c hG p
      (sparsePurePolynomialRing_pure A hp) w hw (hterms w hw) (hcol w).1
  convert hsum using 1
  apply Subtype.ext
  simpa [f] using sparseLaurentEval_eq_sum A a x y p

/-- Uniformly high elements of the actual conductor base lie in the ideal of
actual high generators in every containing source ring. -/
theorem sparseConductorBase_high_mem_highIdeal {ι : Type*}
    (v : ι → Valuation K ℝ≥0) (S A : Subring K) [IsDiscreteValuationRing A]
    (hS:∀z:S,z≠0→∀i,0≤realValuationOrder (v i) z)
    (a:ℕ→Kˣ) (x y:Kˣ) (π:A) (hπ:Irreducible π) (c:ℝ) (hc:0≤c)
    (hCS:sparseConductorBase v A a x y π c≤S)
    (hcoeff:∀b:A,b≠0→∃r:ℕ,∀i,realValuationOrder (v i) (b:K)=r)
    (hsep:SparseLaurentSeparated v a x y (2*c))
    {z:K} (hz:z∈sparseConductorBase v A a x y π c)
    (hhigh:z∈realOrderAbove v c) :
    (⟨z,hCS hz⟩:S)∈sparseHighIdeal v S a x y π c := by
  let I := sparseHighIdeal v S a x y π c
  have hAS : A≤S := (sparseConductorBase_coefficient v A a x y π c).trans hCS
  have haS : ∀n,(a n:K)∈S := fun n => hCS (sparseConductorBase_variable v A a x y π c n)
  have hG : sparseHighGenerators v a x y π c⊆S := fun _ hg =>
    hCS (sparseConductorBase_high v A a x y π c hg)
  obtain ⟨p,hp,b,hb,heq⟩ := sparseConductorBase_pure_decomposition v A S a x y π c hCS I
    (fun _ hg => Ideal.subset_span hg) hz
  have hbhigh : (b:K)∈realOrderAbove v c := by
    by_cases hb0:b=0
    · left
      exact congrArg Subtype.val hb0
    · right
      exact sparseHighIdeal_high v S hS a x y π c hb hb0
  have hphigh : sparseLaurentEval A a x y p∈realOrderAbove v c := by
    have h := (realOrderAbove v c).sub_mem hhigh hbhigh
    rwa [heq,add_sub_cancel_right] at h
  have hpI := sparsePure_eval_mem_highIdeal v S A hAS hS a haS x y π hπ c hc hG
    hcoeff hsep p hp hphigh
  convert I.add_mem hpI hb using 1
  apply Subtype.ext
  exact heq

/-- Adding a high term preserves a low nonzero value. -/
theorem realValuationOrder_add_high_of_low (v:Valuation K ℝ≥0) (c:ℝ)
    {q b:K} (hq:q≠0) (hlo:realValuationOrder v q≤c)
    (hb:b=0 ∨ c<realValuationOrder v b) :
    q+b≠0 ∧ realValuationOrder v (q+b)=realValuationOrder v q := by
  by_cases hb0:b=0
  · simpa [hb0] using (And.intro hq (rfl : realValuationOrder v q=realValuationOrder v q))
  have hlt := hlo.trans_lt (hb.resolve_left hb0)
  obtain ⟨hs0,hs⟩ := realValuationOrder_add_eq_min v hq hb0 (ne_of_lt hlt)
  exact ⟨hs0,hs.trans (min_eq_left hlt.le)⟩

/-- A fixed polynomial representative modulo the high ideal has exactly the
same value as its source element at every branch where that element is low. -/
theorem sparsePure_value_of_low_mod_high {ι : Type*}
    (v:ι→Valuation K ℝ≥0) (A:Subring K) (a:ℕ→Kˣ) (x y:Kˣ) (c:ℝ)
    (p:AddMonoidAlgebra A SparseLaurentKey) {z b:K}
    (hz:z=sparseLaurentEval A a x y p+b) (hb:b∈realOrderAbove v c)
    (i:ι) (hz0:z≠0) (hlo:realValuationOrder (v i) z≤c) :
    sparseLaurentEval A a x y p≠0 ∧
      realValuationOrder (v i) (sparseLaurentEval A a x y p)=realValuationOrder (v i) z := by
  have hbneg : -b=0 ∨ c<realValuationOrder (v i) (-b) := by
    rcases hb with rfl | hb
    · exact Or.inl (neg_zero)
    · exact Or.inr (by simpa using hb i)
  have h := realValuationOrder_add_high_of_low (v i) c hz0 hlo hbneg
  simpa [hz,add_assoc] using h

/-- Any fixed low collected term prevents the source element from becoming
high at that branch, even when the polynomial representative is evaluated at
other branches than the one where it was first chosen. -/
theorem sparsePure_fixed_term_persists {ι : Type*}
    (v:ι→Valuation K ℝ≥0) (R A:Subring K) (a:ℕ→Kˣ) (x y:Kˣ)
    (c:ℝ) (hc:0≤c)
    (hcoeff:∀b:A,b≠0→∃r:ℕ,∀i,realValuationOrder (v i) (b:K)=r)
    (hsep:SparseLaurentSeparated v a x y (2*c))
    (p:AddMonoidAlgebra A SparseLaurentKey) (hp:SparseCollected v R A a x y c p)
    {z b:K} (hz:z=sparseLaurentEval A a x y p+b) (hb:b∈realOrderAbove v c)
    (i:ι) {w:SparseLaurentKey} (hw:w∈p.coeff.support)
    (hlo:realValuationOrder (v i) (sparseLaurentTerm A a x y p w)≤c) :
    z≠0 ∧ realValuationOrder (v i) z≤c := by
  obtain ⟨u,_,hu,hp0,heq⟩ := sparseLaurent_leading v R A a x y c hcoeff hsep p hp i hw
    (hlo.trans (by linarith))
  have hpLow : realValuationOrder (v i) (sparseLaurentEval A a x y p)≤c :=
    heq ▸ hu.trans hlo
  have hb' : b=0 ∨ c<realValuationOrder (v i) b := by
    rcases hb with hb | hb
    · exact Or.inl hb
    · exact Or.inr (hb i)
  obtain ⟨hz0,hval⟩ := realValuationOrder_add_high_of_low (v i) c hp0 hpLow hb'
  exact ⟨hz ▸ hz0,hz ▸ hval ▸ hpLow⟩

end HereditaryAtomicity
