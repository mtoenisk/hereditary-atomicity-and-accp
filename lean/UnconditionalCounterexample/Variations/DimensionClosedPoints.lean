import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Algebra.Pi
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Interpolating at a finite family of closed points

The local conductor targets use values in residue fields that can have
degree greater than one. Distinct kernels give simultaneous interpolation
by the Chinese remainder theorem. A basis of the product of the residue
fields bounds the degrees of all the necessary corrections.
-/

namespace UnconditionalCounterexample.Variations

open MvPolynomial
open scoped Function

variable {k σ ι : Type*} [Field k]

/-- A finite-dimensional quotient admits polynomial representatives of uniformly bounded degree. -/
theorem exists_degree_bound_of_surjective {E : Type*} [AddCommGroup E] [Module k E]
    [FiniteDimensional k E] (f : MvPolynomial σ k →ₗ[k] E) (hf : Function.Surjective f) :
    ∃ b : ℕ, ∀ y : E, ∃ P : MvPolynomial σ k, P.totalDegree ≤ b ∧ f P = y := by
  classical
  let v := Module.finBasis k E
  choose P hP using (fun i ↦ hf (v i))
  refine ⟨Finset.univ.sup (fun i ↦ (P i).totalDegree), fun y ↦ ?_⟩
  refine ⟨∑ i, v.repr y i • P i, totalDegree_finsetSum_le (fun i _ ↦
    (totalDegree_smul_le ..).trans (Finset.le_sup (f := fun j ↦ (P j).totalDegree)
      (Finset.mem_univ i))), ?_⟩
  simpa only [map_sum, map_smul, hP] using v.sum_repr y

variable [Finite ι] {E : ι → Type*} [∀ i, Field (E i)] [∀ i, Algebra k (E i)]

/-- The values at distinct closed points can be prescribed in their respective residue fields. -/
theorem closedPointValues_surjective (γ : ∀ i, σ → E i)
    (hgen : ∀ i, Algebra.adjoin k (Set.range (γ i)) = ⊤)
    (hdist : Function.Injective (fun i ↦ RingHom.ker (aeval (R := k) (γ i)).toRingHom)) :
    Function.Surjective (AlgHom.pi fun i ↦ aeval (R := k) (γ i)) := by
  classical
  let := Fintype.ofFinite ι
  let ev (i : ι) := aeval (R := k) (γ i)
  let I (i : ι) := RingHom.ker (ev i).toRingHom
  have he (i : ι) : Function.Surjective (ev i) :=
    (AlgHom.range_eq_top _).mp ((aeval_range ..).trans (hgen i))
  have hm (i : ι) : (I i).IsMaximal := RingHom.ker_isMaximal_of_surjective (ev i).toRingHom (he i)
  have hc : Pairwise (IsCoprime on I) := fun i j hij ↦
    Ideal.isCoprime_iff_sup_eq.mpr ((hm i).coprime_of_ne (hm j) (hdist.ne hij))
  intro y
  choose a ha using (fun i ↦ he i (y i))
  obtain ⟨f, hf⟩ := Ideal.exists_forall_sub_mem_ideal hc a
  refine ⟨f, funext fun i ↦ ?_⟩
  have hdiff : ev i (f - a i) = 0 := hf i
  rw [map_sub, sub_eq_zero] at hdiff
  exact hdiff.trans (ha i)

/-- All choices of desired values, and every given leading polynomial, have an additive
correction in degrees bounded independently of those choices. -/
theorem closedPointValues_bounded_correction [∀ i, FiniteDimensional k (E i)]
    (γ : ∀ i, σ → E i) (hgen : ∀ i, Algebra.adjoin k (Set.range (γ i)) = ⊤)
    (hdist : Function.Injective (fun i ↦ RingHom.ker (aeval (R := k) (γ i)).toRingHom)) :
    ∃ b : ℕ, ∀ (L : MvPolynomial σ k) (y : ∀ i, E i),
      ∃ C : MvPolynomial σ k, C.totalDegree ≤ b ∧ ∀ i, aeval (γ i) (L + C) = y i := by
  classical
  let := Fintype.ofFinite ι
  let ev := AlgHom.pi fun i ↦ aeval (R := k) (γ i)
  obtain ⟨b, hb⟩ := exists_degree_bound_of_surjective ev.toLinearMap
    (closedPointValues_surjective γ hgen hdist)
  refine ⟨b, fun L y ↦ ?_⟩
  obtain ⟨C, hC, he⟩ := hb (y - ev L)
  refine ⟨C, hC, fun i ↦ ?_⟩
  have hi : aeval (γ i) C = y i - aeval (γ i) L := congrFun he i
  rw [map_add, hi, add_sub_cancel]

end UnconditionalCounterexample.Variations
