import UnconditionalCounterexample.DirectRadicalConductor
import UnconditionalCounterexample.RationalHull
import UnconditionalCounterexample.LocalInterpolation
import UnconditionalCounterexample.PoleJets
import UnconditionalCounterexample.LocalAlgebra.TransportedIntegralImage
import UnconditionalCounterexample.LocalAlgebra.ScaledTransferConductor

/-!
# The actual integral tensor conductor from extracted words

Section 6 computes the conductor after extension of scalars. T and D are
actual subrings of the rational pole algebra. The integral tensor image is
transported through the proved coefficient-extension equivalence into the
actual p-adic pole subalgebra. Rational hull recovery supplies scalar clearing;
finite tensor sums extend the original D evaluation bounds; the actual
extracted words supply ordinary derivatives and scaled-polynomial transfers.

The two-term transfer identities give a power of the vanishing ideal in the integral
tensor image. Rational hull recovery, original integral values, and the derivative
estimates for the same words then identify the exact paired conductor.
-/

noncomputable section
namespace UnconditionalCounterexample.PoleTensorConductor

open Polynomial TensorProduct LocalAlgebra LocalizedPolynomialJets RadicalConductor Filter

variable (p : ℕ) [Fact p.Prime] (S : Set ℚ[X]) (hS : ∀ f ∈ S, f ≠ 0)

def image (T : Subring (PoleAlgebra.generated S)) :
    Subring (PoleAlgebra.generated (ScalarExtension.extendedSet ℚ ℚ_[p] S)) :=
  TransportedIntegralImage.image p _ _ (ScalarExtension.tensorEquiv ℚ ℚ_[p] S hS) T

def ambientImage (T : Subring (PoleAlgebra.generated S)) : Subring (RatFunc ℚ_[p]) :=
  (image p S hS T).map (PoleAlgebra.generated (ScalarExtension.extendedSet ℚ ℚ_[p] S)).val.toRingHom

theorem coe_mem_ambientImage_iff (T : Subring (PoleAlgebra.generated S))
    (z : PoleAlgebra.generated (ScalarExtension.extendedSet ℚ ℚ_[p] S)) :
    (z : RatFunc ℚ_[p]) ∈ ambientImage p S hS T ↔ z ∈ image p S hS T := by
  constructor
  · rintro ⟨x, hx, hxz⟩
    exact (Subtype.ext hxz : x = z) ▸ hx
  · intro hz
    exact ⟨z, hz, rfl⟩

theorem scalar_mem_ambientImage (T : Subring (PoleAlgebra.generated S))
    (c : ℚ_[p]) (hc : c ∈ PadicInt.subring p) :
    RatFunc.C c ∈ ambientImage p S hS T :=
  (coe_mem_ambientImage_iff p S hS T _).mpr
    (TransportedIntegralImage.scalar_mem p _ _ _ T c hc)

theorem power_clearing_ambientImage (T : Subring (PoleAlgebra.generated S))
    (hhull : RationalHull.hull T = ⊤) :
    ∀ z ∈ PoleAlgebra.generated (ScalarExtension.extendedSet ℚ ℚ_[p] S),
      ∃ n : ℕ, RatFunc.C (p : ℚ_[p]) ^ n * z ∈ ambientImage p S hS T := by
  intro z hz
  obtain ⟨n, hn⟩ := TransportedIntegralImage.exists_power_mul_mem p _ _
    (ScalarExtension.tensorEquiv ℚ ℚ_[p] S hS) T
    (fun b => (RationalHull.mem_hull_iff T b).mp (by rw [hhull]; trivial)) ⟨z, hz⟩
  refine ⟨n, ?_⟩
  simpa only [Subalgebra.coe_mul, Subalgebra.coe_pow, SubringClass.coe_natCast,
    map_natCast] using (coe_mem_ambientImage_iff p S hS T _).mpr hn

theorem power_ideal_subset_of_ambient_multiples
    (T : Subring (PoleAlgebra.generated S)) (a b : ℚ_[p]) (R : ℕ)
    (h : ∀ z ∈ PoleAlgebra.generated (ScalarExtension.extendedSet ℚ ℚ_[p] S),
      ((RatFunc.X - RatFunc.C a) * (RatFunc.X - RatFunc.C b)) ^ R * z ∈
        ambientImage p S hS T) :
    ∀ z ∈ Ideal.span
      {algebraMap ℚ_[p][X] (PoleAlgebra.generated (ScalarExtension.extendedSet ℚ ℚ_[p] S))
        (((X - C a) * (X - C b)) ^ R)}, z ∈ image p S hS T := by
  intro z hz
  obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton.mp hz
  apply (coe_mem_ambientImage_iff p S hS T _).mp
  change algebraMap ℚ_[p][X] (RatFunc ℚ_[p]) (((X - C a) * (X - C b)) ^ R) *
    (r : RatFunc ℚ_[p]) ∈ ambientImage p S hS T
  simpa only [map_pow, map_mul, map_sub, RatFunc.algebraMap_X, RatFunc.algebraMap_C]
    using h r r.property

def value (a : ℚ_[p]) (ha : ∀ f ∈ S, f.eval₂ (algebraMap ℚ ℚ_[p]) a ≠ 0) :
    PoleAlgebra.generated (ScalarExtension.extendedSet ℚ ℚ_[p] S) →ₐ[ℚ_[p]] ℚ_[p] where
  toRingHom := (TrivSqZeroExt.fstHom ℚ_[p] ℚ_[p] ℚ_[p]).toRingHom.comp
    (PoleJets.extendedJet S hS a ha)
  commutes' c := by
    change (PoleJets.extendedJet S hS a ha (algebraMap ℚ_[p] _ c)).fst = c
    rw [PoleJets.extendedJet_scalar]
    rfl

theorem integral_values (T : Subring (PoleAlgebra.generated S))
    (a : ℚ_[p]) (ha : ∀ f ∈ S, f.eval₂ (algebraMap ℚ ℚ_[p]) a ≠ 0)
    (hv : ∀ t : T, ‖RatFunc.eval (algebraMap ℚ ℚ_[p]) a
      ((t : PoleAlgebra.generated S) : RatFunc ℚ)‖ ≤ 1)
    (z : PoleAlgebra.generated (ScalarExtension.extendedSet ℚ ℚ_[p] S))
    (hz : z ∈ image p S hS T) : ‖(PoleJets.extendedJet S hS a ha z).fst‖ ≤ 1 := by
  apply TransportedIntegralImage.norm_values_le_one p _ _
    (ScalarExtension.tensorEquiv ℚ ℚ_[p] S hS) T (value p S hS a ha) _ z hz
  intro t
  change ‖(PoleJets.extendedJet S hS a ha
    (ScalarExtension.tensorEquiv ℚ ℚ_[p] S hS (1 ⊗ₜ[ℚ] (t : PoleAlgebra.generated S)))).fst‖ ≤ 1
  rw [PoleJets.extendedJet_one_tmul_fst]
  exact hv t

theorem unbounded_derivatives (T : Subring (PoleAlgebra.generated S))
    (a : ℚ_[p]) (ha : ∀ f ∈ S, f.eval₂ (algebraMap ℚ ℚ_[p]) a ≠ 0)
    (hd : ∀ N : ℝ, ∃ t : T, N < ‖CurveRecovery.geometricDerivativeAt ℚ_[p]
      ((t : PoleAlgebra.generated S) : RatFunc ℚ) a‖) :
    ∀ N : ℝ, ∃ z ∈ image p S hS T, N < ‖(PoleJets.extendedJet S hS a ha z).snd‖ := by
  intro N
  obtain ⟨t, ht⟩ := hd N
  refine ⟨ScalarExtension.tensorEquiv ℚ ℚ_[p] S hS (1 ⊗ₜ[ℚ] (t : PoleAlgebra.generated S)),
    TransportedIntegralImage.original_mem p _ _ _ T t, ?_⟩
  rwa [PoleJets.extendedJet_one_tmul_snd]

theorem pow_lt_norm_of_valuation_lt_neg (z : ℚ_[p]) (i : ℕ)
    (hz : z.valuation < -(i : ℤ)) : (p : ℝ) ^ i < ‖z‖ := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hz0 : z ≠ 0 := by
    intro h
    simp only [h, Padic.valuation_zero] at hz
    omega
  rw [Padic.norm_eq_zpow_neg_valuation hz0, ← zpow_natCast,
    zpow_lt_zpow_iff_right₀ hp1]
  omega

theorem unbounded_norm_of_escaping_valuation (z : ℕ → ℚ_[p]) (stage : ℕ → ℕ)
    (hstage : Tendsto stage atTop atTop)
    (hz : ∀ᶠ i in atTop, (z i).valuation < -(stage i : ℤ)) :
    ∀ N : ℝ, ∃ i, N < ‖z i‖ := by
  intro N
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt N hp1
  obtain ⟨i, hi, hzi⟩ :=
    ((hstage.eventually (eventually_ge_atTop n)).and hz).exists
  exact ⟨i, hn.trans_le (pow_le_pow_right₀ hp1.le hi) |>.trans
    (pow_lt_norm_of_valuation_lt_neg p (z i) (stage i) hzi)⟩

/-- The ordinary derivatives of the actual extracted rational words escape
every norm bound when their scheduled valuation estimates tend to minus infinity. -/
theorem unbounded_word_derivatives
    (T : Subring (PoleAlgebra.generated S)) (y : ℕ → T)
    (F H : ℕ → ℚ[X]) (m stage : ℕ → ℕ) (a : ℚ_[p])
    (hH : ∀ i, (H i).eval₂ (algebraMap ℚ ℚ_[p]) a ≠ 0)
    (hword : ∀ i, ((y i : PoleAlgebra.generated S) : RatFunc ℚ) =
      algebraMap ℚ[X] (RatFunc ℚ) (F i) ^ m i / algebraMap ℚ[X] (RatFunc ℚ) (H i))
    (hstage : Tendsto stage atTop atTop)
    (hd : ∀ᶠ i in atTop,
      (LocalInterpolation.wordDerivative ((F i).map (algebraMap ℚ ℚ_[p]))
        ((H i).map (algebraMap ℚ ℚ_[p])) (m i) a).valuation < -(stage i : ℤ)) :
    ∀ N : ℝ, ∃ t : T, N < ‖CurveRecovery.geometricDerivativeAt ℚ_[p]
      ((t : PoleAlgebra.generated S) : RatFunc ℚ) a‖ := by
  have heq (i : ℕ) : CurveRecovery.geometricDerivativeAt ℚ_[p]
      ((y i : PoleAlgebra.generated S) : RatFunc ℚ) a =
      LocalInterpolation.wordDerivative ((F i).map (algebraMap ℚ ℚ_[p]))
        ((H i).map (algebraMap ℚ ℚ_[p])) (m i) a := by
    rw [hword, RationalFunctionJets.derivative_word _ _ _ _ (hH i)]
    simp only [LocalInterpolation.wordDerivative, derivative_pow, eval_mul, eval_pow,
      eval_C, eval_map, derivative_map, mul_assoc]
  intro N
  obtain ⟨i, hi⟩ := unbounded_norm_of_escaping_valuation p
    (fun i => LocalInterpolation.wordDerivative ((F i).map (algebraMap ℚ ℚ_[p]))
      ((H i).map (algebraMap ℚ ℚ_[p])) (m i) a) stage hstage hd N
  exact ⟨y i, by rwa [heq]⟩

/-- The actual integral tensor image has the paired conductor once the
extracted words supply an initial ideal power and unbounded ordinary rational
derivatives. Integral values are assumed only on the original containing D. -/
theorem conductor_eq_pair
    (T D : Subring (PoleAlgebra.generated S)) (hTD : T ≤ D)
    (hhull : RationalHull.hull T = ⊤)
    (a b : ℚ_[p]) (hab : a ≠ b)
    (ha : ∀ f ∈ S, f.eval₂ (algebraMap ℚ ℚ_[p]) a ≠ 0)
    (hb : ∀ f ∈ S, f.eval₂ (algebraMap ℚ ℚ_[p]) b ≠ 0)
    (hva : ∀ d : D, ‖RatFunc.eval (algebraMap ℚ ℚ_[p]) a
      ((d : PoleAlgebra.generated S) : RatFunc ℚ)‖ ≤ 1)
    (hvb : ∀ d : D, ‖RatFunc.eval (algebraMap ℚ ℚ_[p]) b
      ((d : PoleAlgebra.generated S) : RatFunc ℚ)‖ ≤ 1)
    (hda : ∀ N : ℝ, ∃ t : T, N < ‖CurveRecovery.geometricDerivativeAt ℚ_[p]
      ((t : PoleAlgebra.generated S) : RatFunc ℚ) a‖)
    (hdb : ∀ N : ℝ, ∃ t : T, N < ‖CurveRecovery.geometricDerivativeAt ℚ_[p]
      ((t : PoleAlgebra.generated S) : RatFunc ℚ) b‖)
    (R : ℕ)
    (hpower : ∀ z ∈ Ideal.span
      {algebraMap ℚ_[p][X] (PoleAlgebra.generated (ScalarExtension.extendedSet ℚ ℚ_[p] S))
        (((X - C a) * (X - C b)) ^ R)}, z ∈ image p S hS T) :
    conductorIdeal (image p S hS T) = Ideal.span
      {algebraMap ℚ_[p][X] (PoleAlgebra.generated (ScalarExtension.extendedSet ℚ ℚ_[p] S))
        ((X - C a) * (X - C b))} := by
  let A := PoleAlgebra.generated (ScalarExtension.extendedSet ℚ ℚ_[p] S)
  let M := Submonoid.closure (ScalarExtension.extendedSet ℚ ℚ_[p] S)
  let := PoleAlgebra.isLocalization_generated _
    (ScalarExtension.extendedSet_nonzero ℚ ℚ_[p] S hS)
  have hclear (y : PoleAlgebra.generated S) :
      ∃ n : ℕ, 0 < n ∧ (n : PoleAlgebra.generated S) * y ∈ T :=
    (RationalHull.mem_hull_iff T y).mp (by rw [hhull]; trivial)
  exact DirectConductor.localized_conductor_eq_pair_direct M
    (PadicInt.subring p) (fun _ => PadicInt.mem_subring_iff p)
    (image p S hS T) a b hab
    (PoleJets.closure_eval_ne_zero _ a (PoleJets.extended_retained S a ha))
    (PoleJets.closure_eval_ne_zero _ b (PoleJets.extended_retained S b hb))
    (TransportedIntegralImage.scalar_mem p _ _ _ T)
    (TransportedIntegralImage.exists_scalar_mul_mem p _ _ _ T hclear)
    (integral_values p S hS T a ha (fun t => hva ⟨t, hTD t.property⟩))
    (integral_values p S hS T b hb (fun t => hvb ⟨t, hTD t.property⟩))
    (unbounded_derivatives p S hS T a ha hda)
    (unbounded_derivatives p S hS T b hb hdb) R hpower

/-- The ordinary rational derivatives and two-term transfer identities for the same
extracted words determine the conductor of the integral tensor image. -/
theorem conductor_eq_pair_of_extracted_words
    (T D : Subring (PoleAlgebra.generated S)) (hTD : T ≤ D)
    (hhull : RationalHull.hull T = ⊤)
    (a b : ℚ_[p]) (hab : a ≠ b)
    (haO : a ∈ PadicInt.subring p) (hbO : b ∈ PadicInt.subring p)
    (ha : ∀ f ∈ S, f.eval₂ (algebraMap ℚ ℚ_[p]) a ≠ 0)
    (hb : ∀ f ∈ S, f.eval₂ (algebraMap ℚ ℚ_[p]) b ≠ 0)
    (hva : ∀ d : D, ‖RatFunc.eval (algebraMap ℚ ℚ_[p]) a
      ((d : PoleAlgebra.generated S) : RatFunc ℚ)‖ ≤ 1)
    (hvb : ∀ d : D, ‖RatFunc.eval (algebraMap ℚ ℚ_[p]) b
      ((d : PoleAlgebra.generated S) : RatFunc ℚ)‖ ≤ 1)
    (y : ℕ → T) (F H : ℕ → ℚ[X]) (m stage : ℕ → ℕ) (R : ℕ)
    (hHa : ∀ i, (H i).eval₂ (algebraMap ℚ ℚ_[p]) a ≠ 0)
    (hHb : ∀ i, (H i).eval₂ (algebraMap ℚ ℚ_[p]) b ≠ 0)
    (hword : ∀ i, ((y i : PoleAlgebra.generated S) : RatFunc ℚ) =
      algebraMap ℚ[X] (RatFunc ℚ) (F i) ^ m i / algebraMap ℚ[X] (RatFunc ℚ) (H i))
    (hstage : Tendsto stage atTop atTop) (hm : ∀ᶠ i in atTop, m i ≤ R)
    (hda : ∀ᶠ i in atTop,
      (LocalInterpolation.wordDerivative ((F i).map (algebraMap ℚ ℚ_[p]))
        ((H i).map (algebraMap ℚ ℚ_[p])) (m i) a).valuation < -(stage i : ℤ))
    (hdb : ∀ᶠ i in atTop,
      (LocalInterpolation.wordDerivative ((F i).map (algebraMap ℚ ℚ_[p]))
        ((H i).map (algebraMap ℚ ℚ_[p])) (m i) b).valuation < -(stage i : ℤ))
    (htransfer : ∀ s : ℕ, ∀ᶠ i in atTop,
      ∃ u v : padicScaledPolynomialRing p s,
        (RatFunc.C (p : ℚ_[p]) ^ (2 * s) *
          ((RatFunc.X - RatFunc.C a) * (RatFunc.X - RatFunc.C b))) ^ m i =
        RatFunc.C (p : ℚ_[p]) ^ stage i * ((u : RatFunc ℚ_[p]) + (v : RatFunc ℚ_[p]) *
          (((F i).map (algebraMap ℚ ℚ_[p]) : RatFunc ℚ_[p]) ^ m i /
            ((H i).map (algebraMap ℚ ℚ_[p]) : RatFunc ℚ_[p])))) :
    conductorIdeal (image p S hS T) = Ideal.span
      {algebraMap ℚ_[p][X] (PoleAlgebra.generated (ScalarExtension.extendedSet ℚ ℚ_[p] S))
        ((X - C a) * (X - C b))} := by
  apply conductor_eq_pair p S hS T D hTD hhull a b hab ha hb hva hvb
    (unbounded_word_derivatives p S T y F H m stage a hHa hword hstage hda)
    (unbounded_word_derivatives p S T y F H m stage b hHb hword hstage hdb) R
  apply power_ideal_subset_of_ambient_multiples p S hS T a b R
  have hclear := power_clearing_ambientImage p S hS T hhull
  obtain ⟨s, hs⟩ := hclear RatFunc.X (PoleAlgebra.X_mem _)
  have hinv : (RatFunc.C (p : ℚ_[p]))⁻¹ ∈
      (PoleAlgebra.generated (ScalarExtension.extendedSet ℚ ℚ_[p] S)).toSubring := by
    change (RatFunc.C (p : ℚ_[p]))⁻¹ ∈
      PoleAlgebra.generated (ScalarExtension.extendedSet ℚ ℚ_[p] S)
    rw [← map_inv₀]
    exact (PoleAlgebra.generated (ScalarExtension.extendedSet ℚ ℚ_[p] S)).algebraMap_mem
      ((p : ℚ_[p])⁻¹)
  apply padic_pair_conductor_power_of_eventual_word_transfers p s R a b haO hbO
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

end UnconditionalCounterexample.PoleTensorConductor
