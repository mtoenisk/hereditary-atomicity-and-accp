import UnconditionalCounterexample.Variations.MultivariateRecovery
import UnconditionalCounterexample.Variations.MultivariateStage

/-!
# A listed word in the geometric fibre

The numerator and denominator of a listed word satisfy the same
polynomial relation after extending coefficients. This transports the
separation and derivative tests of a single stage to the original member
of the word algebra.
-/

namespace UnconditionalCounterexample.MultivariateWordRecovery

open MvPolynomial MultivariateRecovery MultivariateFibres MultivariateStage
open TensorProduct

variable {k K σ : Type*} [Field k] [Field K] [Algebra k K]
variable (M : Submonoid (MvPolynomial σ k)) {B : Type*} [CommRing B] [Algebra k B]
  [Algebra (MvPolynomial σ k) B] [IsScalarTower k (MvPolynomial σ k) B] [IsLocalization M B]
  (E : Type*) [CommRing E] [Algebra K E] [Algebra (MvPolynomial σ K) E]
  [IsScalarTower K (MvPolynomial σ K) E] [IsLocalization (M.map (MvPolynomial.map (algebraMap k K))) E]

@[simp] theorem baseElement_polynomial (p : MvPolynomial σ k) :
    baseElement (K := K) M E (algebraMap (MvPolynomial σ k) B p) =
      algebraMap (MvPolynomial σ K) E (MvPolynomial.map (algebraMap k K) p) := by
  unfold baseElement tensorEquiv
  rw [IsLocalization.tensorProductEquivOfMapIncludeRight_tmul]
  change algebraMap (MvPolynomial σ K) E ((algebraTensorAlgEquiv k K) ((1 : K) ⊗ₜ[k] p)) = _
  simp

private theorem baseElement_mul (a b : B) :
    baseElement (K := K) M E (a*b) = baseElement (K := K) M E a * baseElement (K := K) M E b := by
  unfold baseElement
  rw [← map_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]

private theorem baseElement_pow (a : B) (m : ℕ) :
    baseElement (K := K) M E (a^m) = baseElement (K := K) M E a ^ m := by
  unfold baseElement
  rw [← map_pow, Algebra.TensorProduct.tmul_pow, one_pow]

/-- The same fraction in the extended localization. -/
theorem word_relation (p H : MvPolynomial σ k) (a : ℕ) (w : B)
    (hw : algebraMap (MvPolynomial σ k) B p ^ a = algebraMap (MvPolynomial σ k) B H * w) :
    algebraMap (MvPolynomial σ K) E ((MvPolynomial.map (algebraMap k K) p) ^ a) =
      baseElement (K := K) M E w * algebraMap _ E (MvPolynomial.map (algebraMap k K) H) := by
  have h := congrArg (baseElement (K := K) M E) hw
  simpa only [map_pow, baseElement_pow, baseElement_mul, baseElement_polynomial, mul_comm] using h

variable [Fintype σ]

/-- An actual word satisfying the cleared separation test takes distinct values
at the two retained points. -/
theorem separates {p H : MvPolynomial σ k} {a : ℕ} (w : B)
    (hw : algebraMap (MvPolynomial σ k) B p ^ a = algebraMap (MvPolynomial σ k) B H * w)
    (u v : σ → K) (hu : Retained (M.map (MvPolynomial.map (algebraMap k K))) u)
    (hv : Retained (M.map (MvPolynomial.map (algebraMap k K))) v)
    (hpair : (Test.pair u v a (MvPolynomial.map (algebraMap k K) H)).Holds
      (MvPolynomial.map (algebraMap k K) p)) :
    pointEval _ E u hu (baseElement (K := K) M E w) ≠ pointEval _ E v hv (baseElement (K := K) M E w) := by
  let N := M.map (MvPolynomial.map (algebraMap k K))
  have hu' := congrArg (pointEval N E u hu) (word_relation (K := K) M E p H a w hw)
  have hv' := congrArg (pointEval N E v hv) (word_relation (K := K) M E p H a w hw)
  simp only [pointEval_polynomial, map_mul, map_pow] at hu' hv'
  intro heq
  apply hpair
  rw [hu', hv', heq]
  ring

end UnconditionalCounterexample.MultivariateWordRecovery
