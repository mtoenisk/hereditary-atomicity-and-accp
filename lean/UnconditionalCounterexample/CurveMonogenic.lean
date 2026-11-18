import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.RingTheory.Adjoin.Polynomial.Basic
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic

/-!
# The monogenic step in generic-fibre recovery

After adjoining the rational-function variable, Bézout's identity recovers the
inverses of all factors of a reduced denominator. A pole at infinity makes that
variable integral, so the generated algebra is finite over the coefficient algebra.

The generated pole-algebra identity retains explicit denominator-support
and containment hypotheses. Identification with a particular localization,
and the geometric residue-fibre surjectivity needed to conclude `A = B`,
are separate obligations. No finite generation of `A`, characteristic-zero
hypothesis, or degree restriction on omitted polynomials is used here.
-/

namespace UnconditionalCounterexample.CurveMonogenic

open Polynomial

universe u v

variable {k : Type u} [Field k] {K : Type v} [Field K] [Algebra k K]

/-- Bézout clears the inverse denominator inside the literal subalgebra. -/
theorem inverse_denominator_mem (A : Subalgebra k K) (x : K) (hx : x ∈ A)
    (P Q : Polynomial k) (hPQ : IsCoprime P Q) (hQ : aeval x Q ≠ 0)
    (hfrac : aeval x P / aeval x Q ∈ A) : (aeval x Q)⁻¹ ∈ A := by
  obtain ⟨U, V, hUV⟩ := hPQ
  have hev (f : Polynomial k) : aeval x f ∈ A :=
    (Algebra.adjoin_le (Set.singleton_subset_iff.mpr hx))
      (Polynomial.aeval_mem_adjoin_singleton k x)
  have h := congrArg (aeval x) hUV
  simp only [map_add, map_mul, map_one] at h
  have heq : aeval x U * (aeval x P / aeval x Q) + aeval x V = (aeval x Q)⁻¹ := by
    rw [← one_div, eq_div_iff hQ]
    calc
      (aeval x U * (aeval x P / aeval x Q) + aeval x V) * aeval x Q =
          aeval x U * aeval x P + aeval x V * aeval x Q := by
        rw [add_mul, mul_assoc, div_mul_cancel₀ _ hQ]
      _ = 1 := h
  rw [← heq]
  exact A.add_mem (A.mul_mem (hev U) hfrac) (hev V)

/-- An inverse denominator also recovers the inverse of every polynomial factor. -/
theorem inverse_factor_mem_of_inverse_mem (A : Subalgebra k K) (x : K) (hx : x ∈ A)
    (p Q : Polynomial k) (hpQ : p ∣ Q) (hQ : aeval x Q ≠ 0)
    (hinv : (aeval x Q)⁻¹ ∈ A) : (aeval x p)⁻¹ ∈ A := by
  obtain ⟨H, rfl⟩ := hpQ
  have hH : aeval x H ≠ 0 := by
    apply right_ne_zero_of_mul
    simpa only [map_mul] using hQ
  have hev : aeval x H ∈ A :=
    (Algebra.adjoin_le (Set.singleton_subset_iff.mpr hx))
      (Polynomial.aeval_mem_adjoin_singleton k x)
  have heq : aeval x H * (aeval x (p * H))⁻¹ = (aeval x p)⁻¹ := by
    rw [map_mul, mul_inv_rev, ← mul_assoc, mul_inv_cancel₀ hH, one_mul]
  rw [← heq]
  exact A.mul_mem hev hinv

/-- A rational expression with a pole at infinity gives a genuine integral
equation for its argument over any subalgebra containing that expression. -/
theorem integral_of_numerator_degree_gt (A : Subalgebra k K) (x : K)
    (P Q : Polynomial k) (hdeg : Q.natDegree < P.natDegree)
    (hQ : aeval x Q ≠ 0) (hfrac : aeval x P / aeval x Q ∈ A) :
    IsIntegral A x := by
  let z : A := ⟨aeval x P / aeval x Q, hfrac⟩
  let g : Polynomial A := P.map (algebraMap k A) - C z * Q.map (algebraMap k A)
  have hP : P ≠ 0 := by
    intro h
    simp [h] at hdeg
  have hd : (C z * Q.map (algebraMap k A)).degree <
      (P.map (algebraMap k A)).degree := by
    apply degree_lt_degree
    exact (natDegree_C_mul_le _ _).trans_lt (by simpa using hdeg)
  have hlc : g.leadingCoeff = algebraMap k A P.leadingCoeff := by
    dsimp [g]
    rw [leadingCoeff_sub_of_degree_lt hd, leadingCoeff_map]
  have hg : aeval x g = 0 := by
    dsimp [g]
    simp only [aeval_sub, aeval_mul, aeval_C, aeval_map_algebraMap]
    change aeval x P - (aeval x P / aeval x Q) * aeval x Q = 0
    rw [div_mul_cancel₀ _ hQ, sub_self]
  have hint : IsIntegral A ((algebraMap k K P.leadingCoeff) * x) := by
    simpa only [hlc, Algebra.smul_def, ← IsScalarTower.algebraMap_apply k A K] using
      isIntegral_leadingCoeff_smul g x hg
  apply IsIntegral.of_mul_unit (r := algebraMap k A P.leadingCoeff⁻¹)
      (y := algebraMap k K P.leadingCoeff)
  · rw [← IsScalarTower.algebraMap_apply k A K, ← map_mul,
      inv_mul_cancel₀ (leadingCoeff_ne_zero.mpr hP), map_one]
  · simpa only [mul_comm] using hint

/-- Every denominator of an element of A becomes invertible after adjoining
the literal rational-function variable. -/
theorem inverse_denom_mem_adjoin_X (A : Subalgebra k (RatFunc k))
    (s : RatFunc k) (hs : s ∈ A) :
    (algebraMap (Polynomial k) (RatFunc k) s.denom)⁻¹ ∈
      Algebra.adjoin A ({RatFunc.X} : Set (RatFunc k)) := by
  let E := Algebra.adjoin A ({RatFunc.X} : Set (RatFunc k))
  have hX : (RatFunc.X : RatFunc k) ∈ E := Algebra.subset_adjoin rfl
  have hQ : aeval (RatFunc.X : RatFunc k) s.denom ≠ 0 := by
    simpa only [RatFunc.aeval_X_left_eq_algebraMap] using
      RatFunc.algebraMap_ne_zero s.denom_ne_zero
  have hf : aeval (RatFunc.X : RatFunc k) s.num / aeval RatFunc.X s.denom ∈
      E.restrictScalars k := by
    rw [RatFunc.aeval_X_left_eq_algebraMap, RatFunc.aeval_X_left_eq_algebraMap,
      RatFunc.num_div_denom]
    change (algebraMap A (RatFunc k)) ⟨s, hs⟩ ∈ E
    exact E.algebraMap_mem ⟨s, hs⟩
  change (algebraMap (Polynomial k) (RatFunc k) s.denom)⁻¹ ∈ E.restrictScalars k
  simpa only [RatFunc.aeval_X_left_eq_algebraMap] using
    inverse_denominator_mem (E.restrictScalars k) RatFunc.X hX
      s.num s.denom s.isCoprime_num_denom hQ hf

/-- Every factor of an occurring denominator is invertible in `A[X]`. -/
theorem inverse_denom_factor_mem_adjoin_X (A : Subalgebra k (RatFunc k))
    (s : RatFunc k) (hs : s ∈ A) (p : Polynomial k) (hp : p ∣ s.denom) :
    (algebraMap (Polynomial k) (RatFunc k) p)⁻¹ ∈
      Algebra.adjoin A ({RatFunc.X} : Set (RatFunc k)) := by
  let E := Algebra.adjoin A ({RatFunc.X} : Set (RatFunc k))
  have hX : (RatFunc.X : RatFunc k) ∈ E := Algebra.subset_adjoin rfl
  have hQ : aeval (RatFunc.X : RatFunc k) s.denom ≠ 0 := by
    simpa only [RatFunc.aeval_X_left_eq_algebraMap] using
      RatFunc.algebraMap_ne_zero s.denom_ne_zero
  have hinv : (aeval (RatFunc.X : RatFunc k) s.denom)⁻¹ ∈ E.restrictScalars k := by
    rw [RatFunc.aeval_X_left_eq_algebraMap]
    exact inverse_denom_mem_adjoin_X A s hs
  change (algebraMap (Polynomial k) (RatFunc k) p)⁻¹ ∈ E.restrictScalars k
  simpa only [RatFunc.aeval_X_left_eq_algebraMap] using
    inverse_factor_mem_of_inverse_mem (E.restrictScalars k) RatFunc.X hX p s.denom hp hQ hinv

/-- If the proposed pole ring is generated by `X` and inverses of polynomials
which occur in denominators of members of `A`, then it is literally `A[X]`.
The containment of `A` in that generated ring is a separate explicit hypothesis. -/
theorem adjoin_X_eq_pole_algebra (A : Subalgebra k (RatFunc k))
    (S : Set (Polynomial k))
    (hA : A ≤ Algebra.adjoin k (insert (RatFunc.X : RatFunc k)
      ((fun p : Polynomial k => (algebraMap (Polynomial k) (RatFunc k) p)⁻¹) '' S)))
    (hS : ∀ p ∈ S, ∃ s ∈ A, p ∣ RatFunc.denom s) :
    (Algebra.adjoin A ({RatFunc.X} : Set (RatFunc k))).restrictScalars k =
      Algebra.adjoin k (insert (RatFunc.X : RatFunc k)
        ((fun p : Polynomial k => (algebraMap (Polynomial k) (RatFunc k) p)⁻¹) '' S)) := by
  apply le_antisymm
  · rw [Algebra.restrictScalars_adjoin]
    apply Algebra.adjoin_le
    intro x hx
    rcases hx with hx | hx
    · exact hA hx
    · rcases Set.mem_singleton_iff.mp hx with rfl
      exact Algebra.subset_adjoin (Set.mem_insert _ _)
  · apply Algebra.adjoin_le
    intro x hx
    rcases Set.mem_insert_iff.mp hx with rfl | hx
    · change (RatFunc.X : RatFunc k) ∈ Algebra.adjoin A ({RatFunc.X} : Set (RatFunc k))
      exact Algebra.subset_adjoin rfl
    · obtain ⟨p, hp, rfl⟩ := hx
      obtain ⟨s, hs, hps⟩ := hS p hp
      exact inverse_denom_factor_mem_adjoin_X A s hs p hps

/-- A pole at infinity of an actual member of A makes the literal variable
integral over A, without a prior fraction-field equality or degree restriction
on the omitted polynomials. -/
theorem integral_X_of_pole_at_infinity (A : Subalgebra k (RatFunc k))
    (s : RatFunc k) (hs : s ∈ A) (hdeg : s.denom.natDegree < s.num.natDegree) :
    IsIntegral A (RatFunc.X : RatFunc k) := by
  apply integral_of_numerator_degree_gt A RatFunc.X s.num s.denom hdeg
  · simpa only [RatFunc.aeval_X_left_eq_algebraMap] using
      RatFunc.algebraMap_ne_zero s.denom_ne_zero
  · simpa only [RatFunc.aeval_X_left_eq_algebraMap, RatFunc.num_div_denom] using hs

/-- The monogenic algebra in curve recognition is finite over A. -/
theorem finite_adjoin_X_of_pole_at_infinity (A : Subalgebra k (RatFunc k))
    (s : RatFunc k) (hs : s ∈ A) (hdeg : s.denom.natDegree < s.num.natDegree) :
    Module.Finite A (Algebra.adjoin A ({RatFunc.X} : Set (RatFunc k))) :=
  Algebra.finite_adjoin_simple_of_isIntegral (integral_X_of_pole_at_infinity A s hs hdeg)


end UnconditionalCounterexample.CurveMonogenic
