import HereditaryAtomicity.SparsePureTerms
import HereditaryAtomicity.SparseFactorVectors

/-! # Fixed pure terms prevent branch switching in sparse factorizations -/
open scoped NNReal
noncomputable section
namespace HereditaryAtomicity
variable {K : Type*} [Field K]

theorem sparse_factor_family_contradiction
    {ι α : Type*} [Nonempty ι] [Fintype α]
    (v : ι → Valuation K ℝ≥0) (R A : Subring K)
    (a : ℕ → Kˣ) (x y : Kˣ) (c:ℝ) (hc : 1/4<c)
    (hcoeff : ∀ b:A,b≠0 → ∃ r:ℕ,∀ P,realValuationOrder (v P) (b:K)=r)
    (hinj : SparseRelevantVector.LowInjective (fun n P => realValuationOrder (v P) (a n))
      (fun P => realValuationOrder (v P) x) (fun P => realValuationOrder (v P) y) (2*c))
    (hbudget : ∀ n P,realValuationOrder (v P) (a n)≤sparseProfileBudget n)
    (hx : ∀ P,realValuationOrder (v P) x<2*c)
    (f : α → K) (hf0 : ∀ i,f i≠0)
    (hfpos : ∀ i P,0<realValuationOrder (v P) (f i))
    (hsum : ∀ P,∑ i,realValuationOrder (v P) (f i)=realValuationOrder (v P) x)
    (p q : α → AddMonoidAlgebra A SparseLaurentKey)
    (hp : ∀ i,SparseCollected v R A a x y c (p i))
    (hpeval : ∀ i,sparseLaurentEval A a x y (p i)=f i)
    (hq : ∀ i,SparsePure (q i))
    (hlowq : ∀ i P,realValuationOrder (v P) (f i)≤c →
      ∃ d∈(q i).coeff.support,∃ r:ℕ,
        (∀ Q,realValuationOrder (v Q) ((q i).coeff d:K)=r) ∧
        realValuationOrder (v P) (f i)=
          (r:ℝ)+realValuationOrder (v P) (sparseLaurentMonomial a x y (.ofAdd d)))
    (hhighq : ∀ i P,c<realValuationOrder (v P) (f i) →
      ∀ d∈(q i).coeff.support,c<realValuationOrder (v P) (sparseLaurentTerm A a x y (q i) d))
    (hnotall : ∀ i,¬∀ P,c<realValuationOrder (v P) (f i)) : False := by
  classical
  let γ := fun n P => realValuationOrder (v P) (a n)
  let ξ := fun P => realValuationOrder (v P) x
  let σ := fun P => realValuationOrder (v P) y
  have hsep := sparseLaurentSeparated_of_lowInjective v a x y (2*c) hinj
  have hbound : ∀ i P,realValuationOrder (v P) (f i)≤2*c := by
    intro i P
    calc
      realValuationOrder (v P) (f i) ≤ ∑ j,realValuationOrder (v P) (f j) :=
        Finset.single_le_sum (fun j _ => (hfpos j P).le) (Finset.mem_univ i)
      _ = realValuationOrder (v P) x := hsum P
      _ ≤ 2*c := (hx P).le
  have hvec : ∀ P i,∃ w:SparseRelevantVector,w.Relevant ∧ w.eval γ ξ σ P=
      realValuationOrder (v P) (f i) ∧
      (realValuationOrder (v P) (f i)≤c → w.Pure) := by
    intro P i
    obtain ⟨d,_,r,_,hrel,heval,hpure⟩ := sparseLaurent_low_vector v R A a x y c
      hcoeff hsep (p i) (hp i) P (by rw [hpeval]; exact hf0 i)
      (by rw [hpeval]; exact hbound i P)
    refine ⟨d.vector r,hrel,?_,?_⟩
    · rw [SparseLaurentKey.vector_eval]
      simpa only [hpeval] using heval.symm
    · intro h
      exact hpure (by simpa only [hpeval] using h)
  choose w hw hwval hwlow using hvec
  have hhigh : ∀ P,∃ j:α,c<realValuationOrder (v P) (f j) ∧
      (∀ i,c<realValuationOrder (v P) (f i) → i=j) ∧
      (∀ i,(w P i).scalar=0) ∧
      ∀ i,i≠j → (w P i).Pure ∧ ∀ n,(w P i).powers n=0 ∨ (w P i).powers n=1 := by
    intro P
    obtain ⟨j,_,hj,hu,hs,hp⟩ := SparseRelevantVector.unique_high_factor_of_endpoint_sum
      γ ξ σ c hinj P Finset.univ (fun i => realValuationOrder (v P) (f i)) (w P)
      (fun i _ => hfpos i P) (hsum P) (hx P) (fun i _ => hw P i)
      (fun i _ => hwval P i) (fun i _ => hwlow P i)
    exact ⟨j,hj,fun i => hu i (Finset.mem_univ i),fun i => hs i (Finset.mem_univ i),
      fun i => hp i (Finset.mem_univ i)⟩
  let P₀:ι := Classical.choice inferInstance
  obtain ⟨j,hj,hunique,hscalar,hsquare⟩ := hhigh P₀
  have hothers : ∀ i,i≠j → ∀ Q,realValuationOrder (v Q) (f i)≤c := by
    intro i hij Q
    have hilow : realValuationOrder (v P₀) (f i)≤c :=
      le_of_not_gt (fun h => hij (hunique i h))
    obtain ⟨d,hd,r,hr,heval⟩ := hlowq i P₀ hilow
    have hdPure := hq i d (Finsupp.mem_support_iff.mp hd)
    have hdval : (d.vector r).eval γ ξ σ P₀=realValuationOrder (v P₀) (f i) := by
      rw [SparseLaurentKey.vector_eval]
      exact heval.symm
    have hdw : d.vector r=w P₀ i := hinj P₀ _ _ hdPure.relevant (hw P₀ i)
      (by rw [hdval]; exact hbound i P₀)
      (by rw [hwval]; exact hbound i P₀) (hdval.trans (hwval P₀ i).symm)
    have hbudgetTerm := SparseRelevantVector.eval_pure_squarefree_le_quarter γ ξ σ hbudget
      (d.vector r) hdPure (hdw ▸ hscalar i) (hdw ▸ (hsquare i hij).2) Q
    have hterm : realValuationOrder (v Q) (sparseLaurentTerm A a x y (q i) d)≤1/4 := by
      rw [sparseLaurentTerm_order A a x y (v Q) (q i) hd,hr Q]
      simpa only [γ, ξ, σ, SparseLaurentKey.vector_eval] using hbudgetTerm
    exact le_of_not_gt (fun hi => (not_lt_of_ge hterm) (hc.trans (hhighq i Q hi d hd)))
  apply hnotall j
  intro Q
  obtain ⟨k,hk,_,_,_⟩ := hhigh Q
  have hkj : k=j := by
    by_contra h
    exact (not_lt_of_ge (hothers k h Q)) hk
  simpa only [hkj] using hk

end HereditaryAtomicity
