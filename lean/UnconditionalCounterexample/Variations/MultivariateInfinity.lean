import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.RingTheory.Valuation.LocalSubring
import Mathlib.RingTheory.Valuation.Basic

/-!
# Multivariate poles at infinity

For any valuation subring containing the word algebra, bound a polynomial
by the largest coordinate value raised to its total degree. Linear
independence at infinity supplies a late leading form attaining that bound.
The word degree inequality forces every coordinate into the valuation
subring and hence into the integral closure.
-/

namespace UnconditionalCounterexample.MultivariateInfinity

open MvPolynomial

variable {k L σ : Type*} [Field k] [Field L] [Algebra k L]
variable {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]

/-- Total degree bounds a polynomial at coordinates of valuation at most `g`,
where constants have valuation at most one and `1 ≤ g`. -/
theorem valuation_aeval_le (v : Valuation L Γ) (hconst : ∀ c : k, v (algebraMap k L c) ≤ 1)
    (x : σ → L) (g : Γ) (hg : 1 ≤ g) (hx : ∀ i, v (x i) ≤ g) (p : MvPolynomial σ k) :
    v (aeval x p) ≤ g ^ p.totalDegree := by
  classical
  conv_lhs => rw [p.as_sum, map_sum]
  apply v.map_sum_le
  intro t ht
  rw [aeval_monomial, map_mul, Finsupp.prod, map_prod]
  calc
    _ ≤ 1 * ∏ i ∈ t.support, g ^ t i := by
      apply mul_le_mul' (hconst _)
      apply Finset.prod_le_prod
      intro i _
      rw [map_pow]
      exact pow_le_pow_left' (hx i) _
    _ = g ^ (t.sum fun _ n => n) := by rw [one_mul, Finset.prod_pow_eq_pow_sum]; rfl
    _ ≤ _ := pow_le_pow_right' hg (le_totalDegree ht)

private theorem valuation_sum_lt (v : Valuation L Γ) {g : Γ} (hg : 0 < g)
    {ι : Type*} (s : Finset ι) (f : ι → L) (hf : ∀ i ∈ s, v (f i) < g) :
    v (∑ i ∈ s, f i) < g := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hg
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    apply (v.map_add _ _).trans_lt
    exact max_lt (hf i (Finset.mem_insert_self _ _))
      (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

/-- A family of leading linear forms in general position cannot all evaluate
strictly below the largest coordinate value. The coefficients reconstructing
the coordinates belong to the base field, so this works for valuations of
arbitrary rank. -/
theorem exists_large_linear_form (v : Valuation L Γ)
    (hconst : ∀ c : k, v (algebraMap k L c) ≤ 1) (x : σ → L) (j : σ)
    (g : Γ) (hg : 0 < g) (hj : g = v (x j)) (s : Finset ℕ)
    (l : ℕ → MvPolynomial σ k)
    (hlin : ∃ c : ℕ → k, X j = ∑ i ∈ s, C (c i) * l i) :
    ∃ i ∈ s, g ≤ v (aeval x (l i)) := by
  classical
  by_contra! h
  obtain ⟨c, hc⟩ := hlin
  have hbound := valuation_sum_lt v hg s (fun i => algebraMap k L (c i) * aeval x (l i)) (by
    intro i hi
    rw [map_mul]
    exact (mul_le_mul' (hconst _) le_rfl).trans_lt (by simpa using h i hi))
  have he := congrArg (aeval (R := k) x) hc
  simp only [aeval_X, map_sum, map_mul, aeval_C] at he
  rw [← he, hj] at hbound
  exact (lt_irrefl _ hbound)

/-- Integral coordinates from an unbounded set of listed words. General
position is expressed by linear combinations of every set of `card σ` leading
forms. Polynomial identities and word membership are taken in the same field. -/
theorem integral_coordinates_of_words [Fintype σ]
    (A : Subalgebra k L) (x : σ → L) (F l : ℕ → MvPolynomial σ k) (d : ℕ → ℕ)
    (hl : ∀ i, (l i).totalDegree ≤ 1)
    (htop : ∀ i, ∃ p : MvPolynomial σ k, p.totalDegree < d i ∧ F i = l i ^ d i + p)
    (hlin : ∀ s : Finset ℕ, s.card = Fintype.card σ → ∀ j : σ,
      ∃ c : ℕ → k, X j = ∑ i ∈ s, C (c i) * l i)
    (hwords : {i | ∃ (a : ℕ) (H : MvPolynomial σ k) (w : A),
      H.totalDegree < a * d i ∧ aeval x (F i) ^ a = aeval x H * w}.Infinite)
    (j : σ) : IsIntegral A (x j) := by
  classical
  suffices h : ∀ V : ValuationSubring L, A.toSubring ≤ V.toSubring → x j ∈ V by
    have hx : x j ∈ ⨅ V : {V : ValuationSubring L // (A : Set L) ⊆ V.toSubring}, V.1.toSubring :=
      Subring.mem_iInf.mpr fun V => h V.1 V.2
    rwa [iInf_valuationSubring_superset, show Subring.closure (A : Set L) = A.toSubring from
      Subring.closure_eq A.toSubring] at hx
  intro V hAV
  by_contra h
  let v := V.valuation
  have hconst (c : k) : v (algebraMap k L c) ≤ 1 :=
    V.valuation_le_one ⟨_, hAV (A.algebraMap_mem c)⟩
  have hj : 1 < v (x j) := lt_of_not_ge (fun hle => h (V.mem_of_valuation_le_one _ hle))
  obtain ⟨jmax, _, hh⟩ := Finset.exists_max_image (Finset.univ : Finset σ) (fun i => v (x i))
    ⟨j, Finset.mem_univ j⟩
  let g := v (x jmax)
  have hx (i : σ) : v (x i) ≤ g := hh i (Finset.mem_univ i)
  have hg : 1 < g := hj.trans_le (hx j)
  obtain ⟨s, hs, hscard⟩ := hwords.exists_subset_card_eq (Fintype.card σ)
  obtain ⟨i, hi, hgi⟩ := exists_large_linear_form v hconst x jmax g (zero_lt_one.trans hg)
    rfl s l (hlin s hscard jmax)
  have heq : v (aeval x (l i)) = g := le_antisymm
    ((valuation_aeval_le v hconst x g hg.le hx _).trans (by simpa using pow_le_pow_right' hg.le (hl i))) hgi
  obtain ⟨p, hp, hFi⟩ := htop i
  have hpval : v (aeval x p) < g ^ d i :=
    (valuation_aeval_le v hconst x g hg.le hx p).trans_lt (pow_lt_pow_right₀ hg hp)
  have hFval : v (aeval x (F i)) = g ^ d i := by
    rw [hFi, map_add, map_pow, v.map_add_of_distinct_val (by rw [map_pow, heq]; exact hpval.ne')]
    rw [map_pow, heq, max_eq_left hpval.le]
  obtain ⟨a, H, w, hdeg, hword⟩ := hs hi
  have hval := congrArg v hword
  rw [map_pow, map_mul, hFval, ← pow_mul] at hval
  have hw : v w ≤ 1 := V.valuation_le_one ⟨_, hAV w.property⟩
  have hbound := mul_le_mul' (valuation_aeval_le v hconst x g hg.le hx H) hw
  rw [← hval, mul_one, Nat.mul_comm] at hbound
  exact (pow_lt_pow_right₀ hg hdeg).not_ge hbound

/-- The integral-coordinate conclusion takes place inside the domain being
localized. Passing to its fraction field for the valuative test introduces
no extra denominator in the coefficients of the integral equation. -/
theorem integral_coordinates_in_domain {B : Type*} [CommRing B] [IsDomain B]
    [Algebra k B] [Fintype σ]
    (A : Subalgebra k B) (x : σ → B) (F l : ℕ → MvPolynomial σ k) (d : ℕ → ℕ)
    (hl : ∀ i, (l i).totalDegree ≤ 1)
    (htop : ∀ i, ∃ p : MvPolynomial σ k, p.totalDegree < d i ∧ F i = l i ^ d i + p)
    (hlin : ∀ s : Finset ℕ, s.card = Fintype.card σ → ∀ j : σ,
      ∃ c : ℕ → k, X j = ∑ i ∈ s, C (c i) * l i)
    (hwords : {i | ∃ (a : ℕ) (H : MvPolynomial σ k) (w : A),
      H.totalDegree < a * d i ∧ aeval x (F i) ^ a = aeval x H * w}.Infinite)
    (j : σ) : IsIntegral A (x j) := by
  let L := FractionRing B
  let f := IsScalarTower.toAlgHom k B L
  have hf : Function.Injective f := IsFractionRing.injective B L
  let e := A.equivMapOfInjective f hf
  have hw : {i | ∃ (a : ℕ) (H : MvPolynomial σ k) (w : A.map f),
      H.totalDegree < a * d i ∧ aeval (f ∘ x) (F i) ^ a = aeval (f ∘ x) H * w}.Infinite := by
    apply hwords.mono
    rintro i ⟨a,H,w,hd,h⟩
    refine ⟨a,H,e w,hd,?_⟩
    change aeval (fun n => f (x n)) (F i) ^ a = aeval (fun n => f (x n)) H * f w
    simpa only [map_pow, map_mul, comp_aeval_apply] using congrArg f h
  obtain ⟨p, hp, hpx⟩ := integral_coordinates_of_words (A.map f) (f ∘ x) F l d hl htop hlin hw j
  refine ⟨p.map e.symm.toRingHom, hp.map _, hf ?_⟩
  change f.toRingHom _ = f.toRingHom 0
  rw [Polynomial.hom_eval₂, Polynomial.eval₂_map, map_zero]
  have hcoeff : f.toRingHom.comp ((algebraMap A B).comp e.symm.toRingHom) = algebraMap (A.map f) L := by
    ext z
    exact congrArg Subtype.val (e.apply_symm_apply z)
  rw [RingHom.comp_assoc, hcoeff]
  exact hpx

/-- The scheduled rational leading form at index `i`. -/
noncomputable def vandermondeForm (r i : ℕ) : MvPolynomial (Fin r) k :=
  ∑ j : Fin r, C ((i : k) ^ (j : ℕ)) * X j

/-- Vandermonde interpolation expresses every coordinate as a combination
of the leading forms at any `r` distinct stage indices. -/
theorem vandermondeForm_spans [CharZero k] (r : ℕ) (s : Finset ℕ) (hs : s.card = r) (j : Fin r) :
    ∃ c : ℕ → k, X j = ∑ i ∈ s, C (c i) * vandermondeForm r i := by
  classical
  let e := s.orderIsoOfFin hs
  let α : Fin r → k := fun i => ((e i).val : k)
  have hα : Function.Injective α := fun i j h => e.injective (Subtype.ext (Nat.cast_injective h))
  have hu : IsUnit (Matrix.vandermonde α) := (Matrix.isUnit_iff_isUnit_det _).mpr
    (isUnit_iff_ne_zero.mpr (Matrix.det_vandermonde_ne_zero_iff.mpr hα))
  obtain ⟨b, hb⟩ := (Matrix.vecMul_surjective_iff_isUnit.mpr hu) (Pi.single j 1)
  let c (n : ℕ) := if hn : n ∈ s then b (e.symm ⟨n,hn⟩) else 0
  refine ⟨c, ?_⟩
  have hsum : ∑ i ∈ s, C (c i) * vandermondeForm r i =
      ∑ i : Fin r, C (b i) * vandermondeForm r (e i).val := by
    rw [← Finset.sum_attach]
    change (∑ i : s, _) = _
    rw [← e.toEquiv.sum_comp]
    simp [c]
  rw [hsum]
  simp only [vandermondeForm, Finset.mul_sum, ← mul_assoc, ← map_mul]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul, ← map_sum]
  have hcoeff (z : Fin r) : ∑ i : Fin r, b i * (((e i).val : k) ^ (z : ℕ)) = (Pi.single j (1 : k) : Fin r → k) z :=
    congrFun hb z
  simp [hcoeff, Pi.single_apply, apply_ite C, ite_mul]

end UnconditionalCounterexample.MultivariateInfinity
