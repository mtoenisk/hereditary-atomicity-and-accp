import UnconditionalCounterexample.CurveRecovery
import UnconditionalCounterexample.RationalFunctionJets
import UnconditionalCounterexample.RationalHull
import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# Recovering the generic fibre from actual escaping words

Fractions of the form Fⁿ/H provide the poles, point separation, and tangent conditions
for curve recognition. The resulting equality of the rational hull with the pole
algebra puts a positive integer multiple of the coordinate in the original subring.

Construction of the actual escaping sequence remains an explicit producer
obligation. None of these theorems assumes rational-hull equality, integer
clearing, or finite generation as a geometric input.
-/

namespace UnconditionalCounterexample.GenericRecovery

open Polynomial Filter

variable (K : Type) [Field K] [Algebra ℚ K] [IsAlgClosed K]
variable (S : Set ℚ[X])

/-- Actual subring elements supplying the geometric data recover its rational
hull. No rational-hull equality or denominator clearing is assumed. -/
theorem hull_eq_top_of_geometric_poles
    (hS : ∀ p ∈ S, p ≠ 0)
    (α₀ : K) (hα₀ : ∀ p ∈ S, p.eval₂ (algebraMap ℚ K) α₀ ≠ 0)
    (T : Subring (PoleAlgebra.generated S))
    (hpoles : ∀ p ∈ S, ∃ a : T, p ∣ ((a : PoleAlgebra.generated S) : RatFunc ℚ).denom)
    (s : T) (hdeg : (((s : PoleAlgebra.generated S) : RatFunc ℚ).denom.natDegree) <
      (((s : PoleAlgebra.generated S) : RatFunc ℚ).num.natDegree))
    (hsep : ∀ α β : K,
      (∀ p ∈ S, p.eval₂ (algebraMap ℚ K) α ≠ 0) →
      (∀ p ∈ S, p.eval₂ (algebraMap ℚ K) β ≠ 0) → α ≠ β → ∃ a : T,
        RatFunc.eval (algebraMap ℚ K) α ((a : PoleAlgebra.generated S) : RatFunc ℚ) ≠
          RatFunc.eval (algebraMap ℚ K) β ((a : PoleAlgebra.generated S) : RatFunc ℚ))
    (htangent : ∀ α : K, (∀ p ∈ S, p.eval₂ (algebraMap ℚ K) α ≠ 0) → ∃ a : T,
      CurveRecovery.geometricDerivativeAt K ((a : PoleAlgebra.generated S) : RatFunc ℚ) α ≠ 0) :
    RationalHull.hull T = ⊤ := by
  let lift : T → RationalHull.hull T := fun a => ⟨a, Algebra.subset_adjoin a.property⟩
  refine CurveRecovery.subalgebra_eq_top_of_geometric_poles S K hS α₀ hα₀
    (RationalHull.hull T) ?_ (lift s) hdeg ?_ ?_
  · intro p hp
    obtain ⟨a, ha⟩ := hpoles p hp
    exact ⟨lift a, ha⟩
  · intro α β hα hβ hne
    obtain ⟨a, ha⟩ := hsep α β hα hβ hne
    exact ⟨lift a, ha⟩
  · intro α hα
    obtain ⟨a, ha⟩ := htangent α hα
    exact ⟨lift a, ha⟩

/-- A single sequence of actual subring elements with the eventual geometric
properties from the schedule supplies every curve recognition witness. -/
theorem hull_eq_top_of_eventually_geometric_sequence
    (hS : ∀ p ∈ S, p ≠ 0)
    (α₀ : K) (hα₀ : ∀ p ∈ S, p.eval₂ (algebraMap ℚ K) α₀ ≠ 0)
    (T : Subring (PoleAlgebra.generated S)) (y : ℕ → T)
    (hpoles : ∀ p ∈ S, ∀ᶠ n in atTop,
      p ∣ ((y n : PoleAlgebra.generated S) : RatFunc ℚ).denom)
    (hinfinity : ∀ᶠ n in atTop,
      (((y n : PoleAlgebra.generated S) : RatFunc ℚ).denom.natDegree) <
        (((y n : PoleAlgebra.generated S) : RatFunc ℚ).num.natDegree))
    (hsep : ∀ α β : K,
      (∀ p ∈ S, p.eval₂ (algebraMap ℚ K) α ≠ 0) →
      (∀ p ∈ S, p.eval₂ (algebraMap ℚ K) β ≠ 0) → α ≠ β → ∀ᶠ n in atTop,
        RatFunc.eval (algebraMap ℚ K) α ((y n : PoleAlgebra.generated S) : RatFunc ℚ) ≠
          RatFunc.eval (algebraMap ℚ K) β ((y n : PoleAlgebra.generated S) : RatFunc ℚ))
    (htangent : ∀ α : K, (∀ p ∈ S, p.eval₂ (algebraMap ℚ K) α ≠ 0) → ∀ᶠ n in atTop,
      CurveRecovery.geometricDerivativeAt K ((y n : PoleAlgebra.generated S) : RatFunc ℚ) α ≠ 0) :
    RationalHull.hull T = ⊤ := by
  obtain ⟨n, hn⟩ := hinfinity.exists
  refine hull_eq_top_of_geometric_poles K S hS α₀ hα₀ T ?_ (y n) hn ?_ ?_
  · intro p hp
    obtain ⟨i, hi⟩ := (hpoles p hp).exists
    exact ⟨y i, hi⟩
  · intro α β hα hβ hne
    obtain ⟨i, hi⟩ := (hsep α β hα hβ hne).exists
    exact ⟨y i, hi⟩
  · intro α hα
    obtain ⟨i, hi⟩ := (htangent α hα).exists
    exact ⟨y i, hi⟩

/-- The actual scheduled polynomial fractions recover the generic fibre. Every
input is about their explicit numerator, denominator, degree, or finite geometric
test; no rational-function pole or derivative conclusion is assumed. -/
theorem hull_eq_top_of_eventually_tested_words
    (hS : ∀ p ∈ S, p ≠ 0)
    (α₀ : K) (hα₀ : ∀ p ∈ S, p.eval₂ (algebraMap ℚ K) α₀ ≠ 0)
    (T : Subring (PoleAlgebra.generated S)) (y : ℕ → T)
    (F H : ℕ → ℚ[X]) (m : ℕ → ℕ)
    (hword : ∀ n, ((y n : PoleAlgebra.generated S) : RatFunc ℚ) =
      (algebraMap ℚ[X] (RatFunc ℚ) (F n)) ^ m n / algebraMap ℚ[X] (RatFunc ℚ) (H n))
    (hF : ∀ᶠ n in atTop, F n ≠ 0)
    (hH : ∀ᶠ n in atTop, H n ≠ 0)
    (hcoprime : ∀ᶠ n in atTop, IsCoprime (F n ^ m n) (H n))
    (hfactor : ∀ p ∈ S, ∀ᶠ n in atTop, p ∣ H n)
    (hdegree : ∀ᶠ n in atTop, (H n).natDegree < m n * (F n).natDegree)
    (hpair : ∀ α β : K,
      (∀ p ∈ S, p.eval₂ (algebraMap ℚ K) α ≠ 0) →
      (∀ p ∈ S, p.eval₂ (algebraMap ℚ K) β ≠ 0) → α ≠ β → ∀ᶠ n in atTop,
        (SeparationExclusions.Test.pair α β (m n) ((H n).map (algebraMap ℚ K))).Valid ∧
        SeparationExclusions.Test.Holds ((F n).map (algebraMap ℚ K))
          (.pair α β (m n) ((H n).map (algebraMap ℚ K))))
    (htangent : ∀ α : K, (∀ p ∈ S, p.eval₂ (algebraMap ℚ K) α ≠ 0) → ∀ᶠ n in atTop,
      (SeparationExclusions.Test.tangent α (m n) ((H n).map (algebraMap ℚ K))).Valid ∧
      SeparationExclusions.Test.Holds ((F n).map (algebraMap ℚ K))
        (.tangent α (m n) ((H n).map (algebraMap ℚ K)))) :
    RationalHull.hull T = ⊤ := by
  apply hull_eq_top_of_eventually_geometric_sequence K S hS α₀ hα₀ T y
  · intro p hp
    filter_upwards [hH, hcoprime, hfactor p hp] with n hnH hnC hnp
    rw [hword]
    exact RationalFunctionJets.factor_dvd_word_denom (F n) (H n) p (m n) hnH hnC hnp
  · filter_upwards [hF, hH, hdegree] with n hnF hnH hnd
    rw [hword]
    exact RationalFunctionJets.word_pole_at_infinity (F n) (H n) (m n) hnF hnH hnd
  · intro α β hα hβ hne
    filter_upwards [hpair α β hα hβ hne] with n hn
    rw [hword]
    have hHα : (H n).eval₂ (algebraMap ℚ K) α ≠ 0 := by
      simpa only [eval_map] using hn.1.2.2.1
    have hHβ : (H n).eval₂ (algebraMap ℚ K) β ≠ 0 := by
      simpa only [eval_map] using hn.1.2.2.2
    exact RationalFunctionJets.eval_ne_of_pair_test (F n) (H n) (m n) α β hHα hHβ hn.2
  · intro α hα
    filter_upwards [htangent α hα] with n hn
    rw [hword]
    have hHα : (H n).eval₂ (algebraMap ℚ K) α ≠ 0 := by
      simpa only [eval_map] using hn.1.2
    exact RationalFunctionJets.derivative_ne_zero_of_tangent_test (F n) (H n) (m n) α hHα hn.2

/-- Once the generic fibre is recovered, the coordinate has a positive integer
multiple in T, with the same literal ambient inclusion. -/
theorem exists_nat_coordinate_mem (T : Subring (PoleAlgebra.generated S))
    (hT : RationalHull.hull T = ⊤) :
    ∃ n : ℕ, 0 < n ∧ (n : PoleAlgebra.generated S) * CurveRecovery.coordinate S ∈ T :=
  RationalHull.exists_nat_mul_mem_of_hull_eq_top T hT (CurveRecovery.coordinate S)

end UnconditionalCounterexample.GenericRecovery
