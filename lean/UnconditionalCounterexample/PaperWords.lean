import UnconditionalCounterexample.PaperConstruction
import UnconditionalCounterexample.ConstructionRecovery
import UnconditionalCounterexample.SequenceLocalTransfer

/-!
# The geometric and local assertions for every listed word

These conclusions of Proposition 3.1 quantify over the entire list at each
late stage. The same rational word is used for its canonical denominator,
its value at each retained point, and its ordinary derivative.
-/

noncomputable section
namespace UnconditionalCounterexample.PaperWords

open Polynomial Filter ConstructionWords PaperConstruction GlobalPlans GeometricReservations

abbrev plan (n : ℕ) := globalPlan construction n
abbrev denominator (n : ℕ) (w : Word n) := (plan n).wordDen w
abbrev K := AlgebraicClosure ℚ

def word (n : ℕ) (w : Word n) : RatFunc ℚ :=
  ScheduledRecovery.generators raw exponent n ^ w.latestExponent *
    ∏ j ∈ Finset.range n, ScheduledRecovery.generators raw exponent j ^ w.oldExponent j

theorem word_eq_fraction (n : ℕ) (w : Word n) : word n w =
    algebraMap ℚ[X] (RatFunc ℚ) (raw n) ^ w.latestExponent /
      algebraMap ℚ[X] (RatFunc ℚ) (denominator n w) := by
  have h := ConstructionRecovery.global_word_eq_fraction raw exponent n (plan n)
    (globalPlan_E construction n) w
  rwa [ConstructionRecovery.oldDenominator_eq_wordDen] at h

theorem denominator_monic (n : ℕ) (w : Word n) : (denominator n w).Monic :=
  monic_prod_of_monic _ _ (fun j _ => (construction.chain.raw_monic j.val).pow _)

theorem pole_at_infinity (n : ℕ) (w : Word n) :
    (word n w).denom.natDegree < (word n w).num.natDegree := by
  rw [word_eq_fraction]
  apply RationalFunctionJets.word_pole_at_infinity _ _ _ (construction.chain.raw_monic n).ne_zero
    (denominator_monic n w).ne_zero
  rw [globalPlan_degree construction n]
  exact (plan n).infinity w

theorem earlier_factor_dvd (n : ℕ) (w : Word n) (j : ℕ) (hj : j < n) :
    raw j ∣ (word n w).denom := by
  let d := ConstructionRecovery.extendedPowers (plan n) w
  have he : WordGeometry.oldDenominator raw n d = denominator n w :=
    ConstructionRecovery.oldDenominator_eq_wordDen (plan n) w
  rw [word_eq_fraction, ← he]
  apply RationalFunctionJets.factor_dvd_word_denom _ _ _ _
  · rw [he]; exact (denominator_monic n w).ne_zero
  · exact WordGeometry.fresh_pow_coprime_old_product (Finset.range n) raw (raw n) d _
      (construction.chain.raw_irreducible n) (fun i _ => (construction.chain.raw_monic i).ne_zero)
      (fun _ hi => construction.chain.raw_degree_strict (Finset.mem_range.mp hi))
  · exact WordGeometry.old_factor_dvd_product (Finset.range n) raw d j (Finset.mem_range.mpr hj)
      (ConstructionRecovery.extendedPowers_pos (plan n) w j hj)

theorem pole_at_earlier_root (n : ℕ) (w : Word n) (j : ℕ) (hj : j < n)
    (a : K) (ha : (raw j).eval₂ (algebraMap ℚ K) a = 0) :
    (word n w).denom.eval₂ (algebraMap ℚ K) a = 0 := by
  obtain ⟨g, hg⟩ := earlier_factor_dvd n w j hj
  rw [hg, eval₂_mul, ha, zero_mul]

def Retained (a : K) : Prop := ∀ j, (raw j).eval₂ (algebraMap ℚ K) a ≠ 0

private theorem denominator_eval (n : ℕ) (w : Word n) (a : K) (ha : Retained a) :
    (denominator n w).eval₂ (algebraMap ℚ K) a ≠ 0 := by
  apply GeometricReservations.old_product_eval_ne_zero raw n a (fun j _ => ha j)

theorem eventually_separates (a b : K) (hab : a ≠ b) (ha : Retained a) (hb : Retained b) :
    ∀ᶠ n in atTop, ∀ w : Word n, RatFunc.eval (algebraMap ℚ K) a (word n w) ≠
      RatFunc.eval (algebraMap ℚ K) b (word n w) := by
  have h := eventually_pair_tests geometricEnumeration geometricEnumeration_surjective raw Word
    (fun _ w => w.latestExponent) (fun n w => (denominator n w).map (algebraMap ℚ K))
    (global_raw_tests construction) a b hab ha hb
  filter_upwards [h] with n hn
  intro w
  rw [word_eq_fraction]
  exact RationalFunctionJets.eval_ne_of_pair_test _ _ _ a b (denominator_eval n w a ha)
    (denominator_eval n w b hb) (hn w)

theorem eventually_nonzero_derivative (a : K) (ha : Retained a) :
    ∀ᶠ n in atTop, ∀ w : Word n, CurveRecovery.geometricDerivativeAt K (word n w) a ≠ 0 := by
  have h := eventually_tangent_tests geometricEnumeration geometricEnumeration_surjective raw Word
    (fun _ w => w.latestExponent) (fun n w => (denominator n w).map (algebraMap ℚ K))
    (global_raw_tests construction) a ha
  filter_upwards [h] with n hn
  intro w
  rw [word_eq_fraction]
  exact RationalFunctionJets.derivative_ne_zero_of_tangent_test _ _ _ a (denominator_eval n w a ha) (hn w)

theorem eventually_derivative_bound (j : ℕ) (b : Bool) :
    ∀ᶠ n in atTop, ∀ w : Word n,
      (CurveRecovery.geometricDerivativeAt ℚ_[(PrimaryChoices.primes j).val] (word n w)
        (SequenceLocalTransfer.branch construction j b)).valuation < -((n + 1 : ℕ) : ℤ) := by
  filter_upwards [SequenceLocalTransfer.eventually_all_word_estimates construction j 0] with n hn
  intro w
  have hd := ((hn w).1 b)
  rw [word_eq_fraction, RationalFunctionJets.derivative_word _ _ _ _
    (SequenceLocalTransfer.global_wordDen_eval_ne_zero construction n w j b)]
  simpa only [LocalInterpolation.wordDerivative, derivative_pow, eval_mul, eval_pow,
    eval_C, eval_map, derivative_map, mul_assoc] using hd

end UnconditionalCounterexample.PaperWords
