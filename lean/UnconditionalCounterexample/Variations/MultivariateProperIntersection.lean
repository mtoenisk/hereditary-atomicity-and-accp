import UnconditionalCounterexample.Variations.MultivariateFibres
import UnconditionalCounterexample.Variations.MultivariateInfinity
import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian

/-!
# Finite intersections of the multivariate raw hypersurfaces

When the leading powers are in independent coordinates, a common point of
the corresponding hypersurfaces has all coordinates integral over the
coefficient field. Applied in the fraction field of a prime quotient,
this makes each prime above the equations maximal. Noetherianity then makes
the common point set finite. This supplies the finite exclusions needed
when choosing the next polynomial.
-/

namespace UnconditionalCounterexample.MultivariateProperIntersection

open MvPolynomial MultivariateInfinity MultivariateFibres

variable {k σ : Type*} [Field k] [Fintype σ]

/-- The common zeros of the equations have integral coordinates in any
field extension, by the valuation test at infinity. -/
theorem integral_of_common_zero {L : Type*} [Field L] [Algebra k L] (x : σ → L)
    (s : Finset ℕ) (F l : ℕ → MvPolynomial σ k) (d : ℕ → ℕ)
    (hl : ∀ i ∈ s, (l i).totalDegree ≤ 1)
    (htop : ∀ i ∈ s, ∃ p : MvPolynomial σ k, p.totalDegree < d i ∧ F i = l i ^ d i + p)
    (hlin : ∀ j : σ, ∃ c : ℕ → k, X j = ∑ i ∈ s, C (c i) * l i)
    (hzero : ∀ i ∈ s, aeval x (F i) = 0) (j : σ) : IsIntegral k (x j) := by
  classical
  let A : Subalgebra k L := ⊥
  apply isIntegral_trans (A := A)
  suffices h : ∀ V : ValuationSubring L, A.toSubring ≤ V.toSubring → x j ∈ V by
    have hx : x j ∈ ⨅ V : {V : ValuationSubring L // (A : Set L) ⊆ V.toSubring}, V.1.toSubring :=
      Subring.mem_iInf.mpr fun V => h V.1 V.2
    rwa [iInf_valuationSubring_superset, show Subring.closure (A : Set L) = A.toSubring from
      Subring.closure_eq A.toSubring] at hx
  intro V hAV
  by_contra h
  let v := V.valuation
  have hconst (c : k) : v (algebraMap k L c) ≤ 1 := V.valuation_le_one ⟨_,hAV (A.algebraMap_mem c)⟩
  have hj : 1 < v (x j) := lt_of_not_ge (fun hle => h (V.mem_of_valuation_le_one _ hle))
  obtain ⟨jmax, _, hh⟩ := Finset.exists_max_image (Finset.univ : Finset σ) (fun i => v (x i))
    ⟨j, Finset.mem_univ j⟩
  let g := v (x jmax)
  have hx (i : σ) : v (x i) ≤ g := hh i (Finset.mem_univ i)
  have hg : 1 < g := hj.trans_le (hx j)
  obtain ⟨i, hi, hgi⟩ := exists_large_linear_form v hconst x jmax g (zero_lt_one.trans hg)
    rfl s l (hlin jmax)
  obtain ⟨p, hp, hFi⟩ := htop i hi
  have heq : v (aeval x (l i)) = g := le_antisymm
    ((valuation_aeval_le v hconst x g hg.le hx _).trans (by simpa using pow_le_pow_right' hg.le (hl i hi))) hgi
  have hpval : v (aeval x p) < g ^ d i :=
    (valuation_aeval_le v hconst x g hg.le hx p).trans_lt (pow_lt_pow_right₀ hg hp)
  have hFval : v (aeval x (F i)) = g ^ d i := by
    rw [hFi, map_add, map_pow, v.map_add_of_distinct_val (by rw [map_pow, heq]; exact hpval.ne')]
    rw [map_pow, heq, max_eq_left hpval.le]
  rw [hzero i hi, map_zero] at hFval
  exact (ne_of_gt (pow_pos (zero_lt_one.trans hg) (d i))) hFval.symm

/-- Every prime above an intersection with independent leading powers is
maximal. The quotient is an integral domain algebraic over a field. -/
theorem prime_isMaximal (s : Finset ℕ) (F l : ℕ → MvPolynomial σ k) (d : ℕ → ℕ)
    (hl : ∀ i ∈ s, (l i).totalDegree ≤ 1)
    (htop : ∀ i ∈ s, ∃ p : MvPolynomial σ k, p.totalDegree < d i ∧ F i = l i ^ d i + p)
    (hlin : ∀ j : σ, ∃ c : ℕ → k, X j = ∑ i ∈ s, C (c i) * l i)
    (P : Ideal (MvPolynomial σ k)) (hP : P.IsPrime) (hF : ∀ i ∈ s, F i ∈ P) : P.IsMaximal := by
  let : P.IsPrime := hP
  let Q := MvPolynomial σ k ⧸ P
  let L := FractionRing Q
  let f := IsScalarTower.toAlgHom k Q L
  let x (j : σ) := Ideal.Quotient.mk P (X j)
  have he : aeval (R := k) x = Ideal.Quotient.mkₐ k P := by ext j; simp [x]
  have hzero (i : ℕ) (hi : i ∈ s) : aeval (f ∘ x) (F i) = 0 := by
    change aeval (fun j => f (x j)) (F i) = 0
    rw [← comp_aeval_apply x f, he]
    change f (Ideal.Quotient.mk P (F i)) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr (hF i hi), map_zero]
  have hint (j : σ) : IsIntegral k (x j) :=
    (isIntegral_algHom_iff f (IsFractionRing.injective Q L)).mp
      (integral_of_common_zero (f ∘ x) s F l d hl htop hlin hzero j)
  let : Algebra.IsIntegral k Q := ⟨by
    intro a
    obtain ⟨p,rfl⟩ := Ideal.Quotient.mk_surjective a
    induction p using MvPolynomial.induction_on with
    | C c => exact isIntegral_algebraMap
    | add p q hp hq => rw [map_add]; exact hp.add hq
    | mul_X p j hp => rw [map_mul]; exact hp.mul (hint j)⟩
  exact Ideal.Quotient.maximal_of_isField P (isField_of_isIntegral_of_isField' (Field.toIsField k))

/-- The next raw must avoid only finitely many points to keep the
`r+1`-fold common zero locus empty. -/
theorem finite_common_zeros (s : Finset ℕ) (F l : ℕ → MvPolynomial σ k) (d : ℕ → ℕ)
    (hl : ∀ i ∈ s, (l i).totalDegree ≤ 1)
    (htop : ∀ i ∈ s, ∃ p : MvPolynomial σ k, p.totalDegree < d i ∧ F i = l i ^ d i + p)
    (hlin : ∀ j : σ, ∃ c : ℕ → k, X j = ∑ i ∈ s, C (c i) * l i) :
    {u : σ → k | ∀ i ∈ s, eval u (F i) = 0}.Finite := by
  classical
  let I := Ideal.span (F '' (s : Set ℕ))
  have hmin (u : σ → k) (hu : ∀ i ∈ s, eval u (F i) = 0) : pointIdeal u ∈ I.minimalPrimes := by
    have hm : (pointIdeal u).IsMaximal :=
      RingHom.ker_isMaximal_of_surjective _ (fun c => ⟨C c, by simp⟩)
    let : (pointIdeal u).IsPrime := hm.isPrime
    have hle : I ≤ pointIdeal u := Ideal.span_le.mpr (by rintro _ ⟨i,hi,rfl⟩; exact hu i hi)
    obtain ⟨P, hP, hp⟩ := Ideal.exists_minimalPrimes_le hle
    have hmax := prime_isMaximal s F l d hl htop hlin P hP.isPrime
      (fun i hi => hP.le (Ideal.subset_span ⟨i,hi,rfl⟩))
    exact hmax.eq_of_le hm.ne_top hp ▸ hP
  have hinj : Function.Injective (pointIdeal (σ := σ) (k := k)) := by
    intro u w h
    ext j
    have hX : X j - C (u j) ∈ pointIdeal u := by change eval u _ = 0; simp
    rw [h] at hX
    change eval w _ = 0 at hX
    simpa [sub_eq_zero, eq_comm] using hX
  exact (I.finite_minimalPrimes_of_isNoetherianRing.preimage hinj.injOn).subset hmin

end UnconditionalCounterexample.MultivariateProperIntersection
