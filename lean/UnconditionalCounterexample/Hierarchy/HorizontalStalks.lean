import UnconditionalCounterexample.Hierarchy.EvaluationRing
import UnconditionalCounterexample.IntersectionSpectrum

/-!
# Horizontal stalks of the polynomial evaluation ring

Inverting the nonzero integers recovers the whole rational polynomial
ring. A maximal ideal away from all rational primes therefore has the
same localization as a nonzero prime of the principal ideal domain ℚ[X].
-/

noncomputable section
namespace UnconditionalCounterexample.Hierarchy

open Polynomial GuardSupport
open scoped nonZeroDivisors

variable (E : EvaluationFibers)
local notation "A" => evaluationPolynomials E

def evaluationIntegers : Submonoid (A) := (nonZeroDivisors ℤ).map (Int.castRingHom (A))

theorem intPolynomial_mem_evaluationPolynomials (f : ℤ[X]) : f.map (algebraMap ℤ ℚ) ∈ A := by
  induction f using Polynomial.induction_on' with
  | add f g hf hg => simpa only [Polynomial.map_add] using (A).add_mem hf hg
  | monomial n z =>
    rw [Polynomial.map_monomial, ← Polynomial.C_mul_X_pow_eq_monomial]
    apply (A).mul_mem _ ((A).pow_mem (X_mem_evaluationPolynomials E) n)
    change C (z : ℚ) ∈ A
    rw [map_intCast]
    exact intCast_mem _ _

theorem evaluationPolynomials_integerLocalization : IsLocalization (evaluationIntegers E) ℚ[X] := by
  apply (isLocalization_iff _ _).mpr
  refine ⟨?_,?_,?_⟩
  · rintro ⟨_,z,hz,rfl⟩
    have h : IsUnit (z : ℚ) := isUnit_iff_ne_zero.mpr (Int.cast_ne_zero.mpr (nonZeroDivisors.ne_zero hz))
    change IsUnit (z : ℚ[X])
    simpa only [map_intCast] using h.map (algebraMap ℚ ℚ[X])
  · intro f
    by_cases hf : f = 0
    · subst f
      exact ⟨⟨0,1⟩,by simp⟩
    obtain ⟨z,g,hz,_,he⟩ := GuardSupport.exists_integer_multiple f hf
    let t : evaluationIntegers E := ⟨(z : A),⟨z,mem_nonZeroDivisors_iff_ne_zero.mpr hz,rfl⟩⟩
    refine ⟨⟨⟨_,intPolynomial_mem_evaluationPolynomials E g⟩,t⟩,?_⟩
    change f * (z : ℚ[X]) = g.map _
    rw [he, map_intCast,mul_comm]
  · intro f g h
    exact ⟨1,by simp [show f = g from Subtype.ext h]⟩

theorem evaluationPolynomials_not_field : ¬ IsField (A) := by
  intro h
  let x : A := ⟨X,X_mem_evaluationPolynomials E⟩
  obtain ⟨y,hy⟩ := h.mul_inv_cancel (a := x) (fun he ↦ (X_ne_zero : (X : ℚ[X]) ≠ 0) (congrArg (A).subtype he))
  exact (Polynomial.not_isUnit_X (R := ℚ)) (isUnit_iff_exists_inv.mpr ⟨y.val, congrArg (A).subtype hy⟩)

theorem evaluationIntegers_disjoint (M : Ideal (A)) [M.IsPrime] (h : ∀ p : PrimeIndex, (p.val : A) ∉ M) :
    Disjoint ((evaluationIntegers E) : Set (A)) (M : Set (A)) := by
  by_contra hmeet
  obtain ⟨_,⟨z,hz,rfl⟩,hzM⟩ := Set.not_disjoint_iff.mp hmeet
  let I : Ideal ℤ := M.comap (Int.castRingHom (A))
  have hzI : z ∈ I := hzM
  have hn : I ≠ ⊥ := fun he ↦ (nonZeroDivisors.ne_zero hz) (by simpa [he] using hzI)
  obtain ⟨a,ha,ha'⟩ := (inferInstance : I.IsPrime).exists_mem_prime_of_ne_bot hn
  apply h ⟨a.natAbs,Int.prime_iff_natAbs_prime.mp ha'⟩
  change ((a.natAbs : ℤ) : A) ∈ M
  change (a.natAbs : ℤ) ∈ I
  rw [Int.natCast_natAbs]
  rcases le_total 0 a with h | h
  · simpa [abs_of_nonneg h] using ha
  · simpa [abs_of_nonpos h] using I.neg_mem ha

theorem horizontal_stalk_isDVR_of_disjoint (M : Ideal (A)) [M.IsMaximal]
    (h : Disjoint ((evaluationIntegers E) : Set (A)) (M : Set (A))) :
    IsDiscreteValuationRing (Localization.AtPrime M) := by
  let := evaluationPolynomials_integerLocalization E
  let Q := M.map (algebraMap (A) ℚ[X])
  let : Q.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint _ ℚ[X] M inferInstance h
  have hc : Q.under (A) = M := IsLocalization.under_map_of_isPrime_disjoint _ ℚ[X] (inferInstance : M.IsPrime) h
  have hm : M ≠ ⊥ := fun he ↦ evaluationPolynomials_not_field E (Ring.isField_iff_maximal_bot.mpr (he ▸ (inferInstance : M.IsMaximal)))
  obtain ⟨x,hx,h0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hm
  have hQ : Q ≠ ⊥ := fun he ↦ h0 (Subtype.ext (show (x : ℚ[X]) = 0 from
    Ideal.mem_bot.mp (he ▸ (Ideal.mem_map_of_mem (algebraMap (A) ℚ[X]) hx : _ ∈ Q))))
  let := IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain ℚ[X] hQ (Localization.AtPrime Q)
  let : IsLocalization.AtPrime (Localization.AtPrime Q) (Q.under (A)) :=
    IsLocalization.isLocalization_isLocalization_atPrime_isLocalization (evaluationIntegers E) (Localization.AtPrime Q) Q
  apply IntersectionSpectrum.stalk_isDVR_of_eq (Q.under (A)) M hc
  exact IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing
    (IsLocalization.algEquiv (Q.under (A)).primeCompl (Localization.AtPrime Q) (Localization.AtPrime (Q.under (A))))

theorem horizontal_stalk_isDVR (M : Ideal (A)) [M.IsMaximal] (h : ∀ p : PrimeIndex, (p.val : A) ∉ M) :
    IsDiscreteValuationRing (Localization.AtPrime M) :=
  horizontal_stalk_isDVR_of_disjoint E M (evaluationIntegers_disjoint E M h)

end UnconditionalCounterexample.Hierarchy
