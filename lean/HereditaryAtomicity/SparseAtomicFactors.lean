import HereditaryAtomicity.SparseCutFactorization
import HereditaryAtomicity.SparsePureIdeal
import Mathlib.Algebra.BigOperators.Fin

/-! # Actual atomic factorizations and sparse conductor cuts -/
open scoped NNReal
noncomputable section
namespace HereditaryAtomicity
variable {K : Type*} [Field K]

theorem exists_fin_atomic_factorization {T:Type*} [CommRing T] [IsDomain T]
    (hT:Factorization.IsAtomicDomain T) (z:T) (hz:z≠0) :
    ∃n:ℕ,∃f:Fin n→T,(∀i,Irreducible (f i)) ∧ Associated (∏i,f i) z := by
  classical
  obtain ⟨s,hs,hprod⟩ := hT z hz
  refine ⟨s.toList.length, s.toList.get, ?_, ?_⟩
  · intro i
    exact hs _ (Multiset.mem_toList.mp (List.get_mem _ _))
  · have heq : (∏i,s.toList.get i)=s.prod := by
      rw [← List.prod_ofFn,List.ofFn_get,Multiset.prod_toList]
    rwa [heq]

/-- Association by an intrinsic unit preserves every branch order. -/
theorem realValuationOrder_eq_of_associated {ι:Type*}
    (v:ι→Valuation K ℝ≥0) (S:Subring K)
    (hS:∀z:S,z≠0→∀P,0≤realValuationOrder (v P) z)
    {z t:S} (hz:z≠0) (h:Associated z t) (P:ι) :
    realValuationOrder (v P) z=realValuationOrder (v P) t := by
  obtain ⟨u,hu⟩ := h
  have huK : (u:S)≠0 := u.ne_zero
  have ho := realValuationOrder_mul (v P) (Subtype.coe_ne_coe.mpr hz)
    (Subtype.coe_ne_coe.mpr huK)
  rw [← Subring.coe_mul,hu,
    realValuationOrder_eq_zero_of_isUnit (v P) S (fun z hz => hS z hz P) u.isUnit,
    add_zero] at ho
  exact ho.symm

/-- An actual cut containing the high generators cannot be atomic when its
irreducibles have numerator representatives from the conductor base. -/
theorem not_isAtomicDomain_sparse_conductor_cut {ι:Type*} [Nonempty ι]
    (v:ι→Valuation K ℝ≥0) (R A S:Subring K) [IsDiscreteValuationRing A]
    (hAR:A≤R) (hR:∀z:K,z∈R→z≠0→∀P,0≤realValuationOrder (v P) z)
    (hS:∀z:S,z≠0→∀P,0≤realValuationOrder (v P) z)
    (hcenter:∀z:S,z≠0→¬IsUnit z→∀P,0<realValuationOrder (v P) z)
    (a:ℕ→Kˣ) (ha:∀n,(a n:K)∈R) (x y:Kˣ) (π:A) (hπ:Irreducible π)
    (c:ℝ) (hc:1/4<c)
    (hreturn:∀z:K,z≠0→(∀P,c<realValuationOrder (v P) z)→z∈R)
    (hCS:sparseConductorBase v A a x y π c≤S)
    (hcoeff:∀b:A,b≠0→∃r:ℕ,∀P,realValuationOrder (v P) (b:K)=r)
    (hinj:SparseRelevantVector.LowInjective (fun n P=>realValuationOrder (v P) (a n))
      (fun P=>realValuationOrder (v P) x) (fun P=>realValuationOrder (v P) y) (2*c))
    (hfinite:∀z:K,z≠0→Set.Finite (Set.range (fun P=>realValuationOrder (v P) z)))
    (hbudget:∀n P,realValuationOrder (v P) (a n)≤sparseProfileBudget n)
    (hpos:∀n P,0<realValuationOrder (v P) (a n))
    (hx:∀P,c<realValuationOrder (v P) x ∧ realValuationOrder (v P) x<2*c)
    (hden:∀z:S,∃f:sparseConductorBase v A a x y π c,
      Associated z (Subring.inclusion hCS f)) :
    ¬Factorization.IsAtomicDomain S := by
  classical
  intro hatomic
  have hc0:0≤c := le_of_lt (by linarith)
  have hsep := sparseLaurentSeparated_of_lowInjective v a x y (2*c) hinj
  have haS:∀n,(a n:K)∈S := fun n=>hCS (sparseConductorBase_variable v A a x y π c n)
  have hG:sparseHighGenerators v a x y π c⊆S := fun _ hz=>
    hCS (sparseConductorBase_high v A a x y π c hz)
  let I := sparseHighIdeal v S a x y π c
  let xS:S := ⟨x,hCS (sparseConductorBase_endpoint v A a x y π c (fun P=>(hx P).1))⟩
  obtain ⟨n,t,ht,htprod⟩ := exists_fin_atomic_factorization hatomic xS
    (Subtype.coe_ne_coe.mp (Units.ne_zero x))
  choose f hf using fun i=>hden (t i)
  let fS:Fin n→S := fun i=>Subring.inclusion hCS (f i)
  have hfIrr:∀i,Irreducible (fS i) := fun i=>(hf i).irreducible (ht i)
  have hf0:∀i,(f i:K)≠0 := fun i=>Subtype.coe_ne_coe.mpr (hfIrr i).ne_zero
  have hfpos:∀i P,0<realValuationOrder (v P) (f i:K) :=
    fun i=>hcenter (fS i) (hfIrr i).ne_zero (hfIrr i).not_isUnit
  have hsum:∀P,∑i,realValuationOrder (v P) (f i:K)=realValuationOrder (v P) x := by
    intro P
    calc
      (∑i,realValuationOrder (v P) (f i:K)) = ∑i,realValuationOrder (v P) (t i:K) := by
        apply Finset.sum_congr rfl
        intro i _
        exact (realValuationOrder_eq_of_associated v S hS (ht i).ne_zero (hf i) P).symm
      _ = realValuationOrder (v P) ((∏i,t i:S):K) := by
        change _ = realValuationOrder (v P) (S.subtype (∏i,t i))
        rw [map_prod]
        exact (realValuationOrder_prod (v P) Finset.univ (fun i=>(t i:K))
          (fun i _=>Subtype.coe_ne_coe.mpr (ht i).ne_zero)).symm
      _ = realValuationOrder (v P) x :=
        realValuationOrder_eq_of_associated v S hS (Finset.prod_ne_zero_iff.mpr
          (fun i _=>(ht i).ne_zero)) htprod P
  have hexp:∀i,∃p:AddMonoidAlgebra A SparseLaurentKey,
      SparseCollected v R A a x y c p ∧ sparseLaurentEval A a x y p=(f i:K) := by
    intro i
    exact sparseConductorBase_representation v R A hAR hR a ha x y π hπ.ne_zero c hreturn (f i).property
  choose p hp hpeval using hexp
  have hexq:∀i,∃q:AddMonoidAlgebra A SparseLaurentKey,q∈sparsePurePolynomialRing A ∧
      ∃b:S,b∈I ∧ (f i:K)=sparseLaurentEval A a x y q+(b:K) := by
    intro i
    exact sparseConductorBase_pure_decomposition v A S a x y π c hCS I
      (fun _ hz=>Ideal.subset_span hz) (f i).property
  choose q hq b hb heq using hexq
  have hqcol:∀i,SparseCollected v R A a x y c (q i) := fun i=>
    sparsePurePolynomialRing_collected v R A hAR hR a ha x y c (hq i)
  have hbhigh:∀i,(b i:K)∈realOrderAbove v c := by
    intro i
    by_cases h:b i=0
    · left
      exact congrArg Subtype.val h
    · right
      exact sparseHighIdeal_high v S hS a x y π c (hb i) h
  apply sparse_factor_family_contradiction v R A a x y c hc hcoeff hinj hbudget
    (fun P=>(hx P).2) (fun i=>(f i:K)) hf0 hfpos hsum p q hp hpeval
    (fun i=>sparsePurePolynomialRing_pure A (hq i))
  · intro i P hlo
    obtain ⟨hq0,hqval⟩ := sparsePure_value_of_low_mod_high v A a x y c (q i)
      (heq i) (hbhigh i) P (hf0 i) hlo
    obtain ⟨d,hd,r,hr,_,hval,_⟩ := sparseLaurent_low_vector v R A a x y c hcoeff hsep
      (q i) (hqcol i) P hq0 (by rw [hqval]; linarith)
    exact ⟨d,hd,r,hr,hqval.symm.trans hval⟩
  · intro i P hhigh d hd
    by_contra h
    have hlo := (sparsePure_fixed_term_persists v R A a x y c hc0 hcoeff hsep
      (q i) (hqcol i) (heq i) (hbhigh i) P hd (le_of_not_gt h)).2
    exact (not_lt_of_ge hlo) hhigh
  · intro i hall
    have hfmem := sparseConductorBase_high_mem_highIdeal v S A hS a x y π hπ c hc0
      hCS hcoeff hsep (f i).property (Or.inr hall)
    exact sparseHighIdeal_not_irreducible v (Classical.choice inferInstance) S hS a haS x y π
      (Subtype.coe_ne_coe.mpr hπ.ne_zero) c hc0 hG hfinite hbudget
      (fun n=>hpos n _) hfmem (hfIrr i)

end HereditaryAtomicity
