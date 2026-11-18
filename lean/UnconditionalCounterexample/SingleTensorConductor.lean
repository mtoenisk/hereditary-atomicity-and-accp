import UnconditionalCounterexample.SingleDirectConductor
import UnconditionalCounterexample.PoleTensorConductor
import UnconditionalCounterexample.LocalAlgebra.SingleScaledTransfer

/-!
# Exact one-point conductor of the integral tensor image

The original subring and its containing domain sit in the actual rational
pole algebra. We use the same proved coefficient-extension embedding and
integral tensor image as the paired construction. Integral original values
and escaping ordinary derivatives give the exact one-point conductor by
direct Taylor cancellation. The final theorem derives the initial ideal
power from the same extracted words and literal single-factor transfers.
-/

noncomputable section
namespace UnconditionalCounterexample.SingleTensorConductor

open Polynomial TensorProduct LocalAlgebra LocalizedPolynomialJets RadicalConductor Filter
open PoleTensorConductor

variable (p : ℕ) [Fact p.Prime] (S : Set ℚ[X]) (hS : ∀ f ∈ S, f ≠ 0)

theorem power_ideal_subset_of_ambient_multiples
    (T : Subring (PoleAlgebra.generated S)) (a : ℚ_[p]) (R : ℕ)
    (h : ∀ z ∈ PoleAlgebra.generated (ScalarExtension.extendedSet ℚ ℚ_[p] S),
      (RatFunc.X - RatFunc.C a) ^ R * z ∈
        ambientImage p S hS T) :
    ∀ z ∈ Ideal.span
      {algebraMap ℚ_[p][X] (PoleAlgebra.generated (ScalarExtension.extendedSet ℚ ℚ_[p] S))
        ((X - C a) ^ R)}, z ∈ image p S hS T := by
  intro z hz
  obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton.mp hz
  apply (coe_mem_ambientImage_iff p S hS T _).mp
  change algebraMap ℚ_[p][X] (RatFunc ℚ_[p]) ((X - C a) ^ R) *
    (r : RatFunc ℚ_[p]) ∈ ambientImage p S hS T
  simpa only [map_pow, map_mul, map_sub, RatFunc.algebraMap_X, RatFunc.algebraMap_C]
    using h r r.property

/-- Original integral values and derivatives determine the actual single-point tensor conductor. -/
theorem conductor_eq_single
    (T D : Subring (PoleAlgebra.generated S)) (hTD : T ≤ D)
    (hhull : RationalHull.hull T = ⊤)
    (a : ℚ_[p])
    (ha : ∀ f ∈ S, f.eval₂ (algebraMap ℚ ℚ_[p]) a ≠ 0)
    (hva : ∀ d : D, ‖RatFunc.eval (algebraMap ℚ ℚ_[p]) a
      ((d : PoleAlgebra.generated S) : RatFunc ℚ)‖ ≤ 1)
    (hda : ∀ N : ℝ, ∃ t : T, N < ‖CurveRecovery.geometricDerivativeAt ℚ_[p]
      ((t : PoleAlgebra.generated S) : RatFunc ℚ) a‖)
    (R : ℕ)
    (hpower : ∀ z ∈ Ideal.span
      {algebraMap ℚ_[p][X] (PoleAlgebra.generated (ScalarExtension.extendedSet ℚ ℚ_[p] S))
        ((X - C a) ^ R)}, z ∈ image p S hS T) :
    conductorIdeal (image p S hS T) = Ideal.span
      {algebraMap ℚ_[p][X] (PoleAlgebra.generated (ScalarExtension.extendedSet ℚ ℚ_[p] S))
        (X - C a)} := by
  let A := PoleAlgebra.generated (ScalarExtension.extendedSet ℚ ℚ_[p] S)
  let M := Submonoid.closure (ScalarExtension.extendedSet ℚ ℚ_[p] S)
  let := PoleAlgebra.isLocalization_generated _
    (ScalarExtension.extendedSet_nonzero ℚ ℚ_[p] S hS)
  have hclear (y : PoleAlgebra.generated S) :
      ∃ n : ℕ, 0 < n ∧ (n : PoleAlgebra.generated S) * y ∈ T :=
    (RationalHull.mem_hull_iff T y).mp (by rw [hhull]; trivial)
  exact DirectConductor.localized_conductor_eq_single_direct M
    (PadicInt.subring p) (fun _ => PadicInt.mem_subring_iff p)
    (image p S hS T) a
    (PoleJets.closure_eval_ne_zero _ a (PoleJets.extended_retained S a ha))
    (TransportedIntegralImage.scalar_mem p _ _ _ T)
    (TransportedIntegralImage.exists_scalar_mul_mem p _ _ _ T hclear)
    (integral_values p S hS T a ha (fun t => hva ⟨t, hTD t.property⟩))
    (unbounded_derivatives p S hS T a ha hda) R hpower


/-- The same extracted words supply the initial ideal power and derivative escape. -/
theorem conductor_eq_single_of_extracted_words
    (T D : Subring (PoleAlgebra.generated S)) (hTD : T ≤ D)
    (hhull : RationalHull.hull T = ⊤)
    (a : ℚ_[p])
    (haO : a ∈ PadicInt.subring p)
    (ha : ∀ f ∈ S, f.eval₂ (algebraMap ℚ ℚ_[p]) a ≠ 0)
    (hva : ∀ d : D, ‖RatFunc.eval (algebraMap ℚ ℚ_[p]) a
      ((d : PoleAlgebra.generated S) : RatFunc ℚ)‖ ≤ 1)
    (y : ℕ → T) (F H : ℕ → ℚ[X]) (m stage : ℕ → ℕ) (R : ℕ)
    (hHa : ∀ i, (H i).eval₂ (algebraMap ℚ ℚ_[p]) a ≠ 0)
    (hword : ∀ i, ((y i : PoleAlgebra.generated S) : RatFunc ℚ) =
      algebraMap ℚ[X] (RatFunc ℚ) (F i) ^ m i / algebraMap ℚ[X] (RatFunc ℚ) (H i))
    (hstage : Tendsto stage atTop atTop) (hm : ∀ᶠ i in atTop, m i ≤ R)
    (hda : ∀ᶠ i in atTop,
      (LocalInterpolation.wordDerivative ((F i).map (algebraMap ℚ ℚ_[p]))
        ((H i).map (algebraMap ℚ ℚ_[p])) (m i) a).valuation < -(stage i : ℤ))
    (htransfer : ∀ s : ℕ, ∀ᶠ i in atTop,
      ∃ u v : padicScaledPolynomialRing p s,
        (RatFunc.C (p : ℚ_[p]) ^ (2 * s) *
          (RatFunc.X - RatFunc.C a)) ^ m i =
        RatFunc.C (p : ℚ_[p]) ^ stage i * ((u : RatFunc ℚ_[p]) + (v : RatFunc ℚ_[p]) *
          (((F i).map (algebraMap ℚ ℚ_[p]) : RatFunc ℚ_[p]) ^ m i /
            ((H i).map (algebraMap ℚ ℚ_[p]) : RatFunc ℚ_[p])))) :
    conductorIdeal (image p S hS T) = Ideal.span
      {algebraMap ℚ_[p][X] (PoleAlgebra.generated (ScalarExtension.extendedSet ℚ ℚ_[p] S))
        (X - C a)} := by
  apply conductor_eq_single p S hS T D hTD hhull a ha hva
    (unbounded_word_derivatives p S T y F H m stage a hHa hword hstage hda) R
  apply power_ideal_subset_of_ambient_multiples p S hS T a R
  have hclear := power_clearing_ambientImage p S hS T hhull
  obtain ⟨s, hs⟩ := hclear RatFunc.X (PoleAlgebra.X_mem _)
  have hinv : (RatFunc.C (p : ℚ_[p]))⁻¹ ∈
      (PoleAlgebra.generated (ScalarExtension.extendedSet ℚ ℚ_[p] S)).toSubring := by
    change (RatFunc.C (p : ℚ_[p]))⁻¹ ∈
      PoleAlgebra.generated (ScalarExtension.extendedSet ℚ ℚ_[p] S)
    rw [← map_inv₀]
    exact (PoleAlgebra.generated (ScalarExtension.extendedSet ℚ ℚ_[p] S)).algebraMap_mem
      ((p : ℚ_[p])⁻¹)
  apply padic_single_conductor_power_of_eventual_word_transfers p s R a haO
    (ambientImage p S hS T) (PoleAlgebra.generated (ScalarExtension.extendedSet ℚ ℚ_[p] S)).toSubring
    (scalar_mem_ambientImage p S hS T) hs hinv hclear stage m
    (fun i => (F i).map (algebraMap ℚ ℚ_[p]))
    (fun i => (H i).map (algebraMap ℚ ℚ_[p])) hstage
  filter_upwards [hm, htransfer s] with i hmi hti
  refine ⟨hmi, ?_, hti⟩
  have hmem := (coe_mem_ambientImage_iff p S hS T _).mpr
    (TransportedIntegralImage.original_mem p _ _
      (ScalarExtension.tensorEquiv ℚ ℚ_[p] S hS) T (y i))
  have hH0 : H i ≠ 0 := by
    intro h
    simpa only [h, eval₂_zero, ne_eq, not_true_eq_false] using hHa i
  have heq := ScalarExtension.embedding_one_tmul_fraction ℚ ℚ_[p] S hS
    (y i) ((F i) ^ m i) (H i) hH0 (by simpa only [map_pow] using hword i)
  change ScalarExtension.embedding ℚ ℚ_[p] S hS
    (1 ⊗ₜ[ℚ] (y i : PoleAlgebra.generated S)) ∈ ambientImage p S hS T at hmem
  rw [heq] at hmem
  simpa only [Polynomial.map_pow, map_pow, RatFunc.coePolynomial_eq_algebraMap] using hmem

end UnconditionalCounterexample.SingleTensorConductor
