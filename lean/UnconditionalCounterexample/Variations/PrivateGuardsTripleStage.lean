import UnconditionalCounterexample.Variations.PrivateGuardsTriple
import UnconditionalCounterexample.Variations.PrivateGuardsMixedTargets
import UnconditionalCounterexample.Variations.MultiDomainFibreTargets

/-! # Arithmetic returns and listed-word tests on the three private branches -/

noncomputable section
namespace UnconditionalCounterexample.Variations.PrivateGuards.Live

open MvPolynomial GuardSupport MultivariateSelection MultiDomain WithZero
open scoped Topology

variable {r n : ℕ} {p : PrimeIndex} {M : ℕ → Type*} {G : Poly r} {tests : Finset (Poly r)}
  (s : Pair p G tests) (g : ScreenedGuard r p)

def tripleValuation (i : Option Bool) : Valuation (g.Field i) ℤᵐ⁰ := by
  cases i with
  | none => exact GuardUnramified.valuation p.val _
  | some b => exact Padic.mulValuation

theorem tripleValuation_prime (i : Option Bool) :
    tripleValuation g i (p.val : g.Field i) = exp (-1) := by
  cases i with
  | none => exact GuardUnramified.valuation_prime p.val _
  | some b => exact EvaluationDVR.valuation_prime p.val (RingHom.id ℚ_[p.val])

theorem tripleValuation_compat (i : Option Bool) (a b : g.Field i) :
    tripleValuation g i a < tripleValuation g i b ↔ ‖a‖ < ‖b‖ := by
  cases i with
  | none => exact (⟨g,none⟩ : Fibre r p).localValuation_compat (extra := false) none a b
  | some t => exact Padic.norm_lt_norm_iff_mulValuation_lt.symm

def tripleEval (i : Option Bool) : Poly r →+* g.Field i :=
  (aeval (R := ℚ) (s.triple g i)).toRingHom

def tripleTarget (h : History r M n) (i : Option Bool) : g.Field i :=
  mixedValue h (tripleEval s g i) (tripleValuation g i) p.val none

theorem tripleTarget_norm (h : History r M n) (i : Option Bool) : ‖tripleTarget s g h i‖ = 1 := by
  have he : tripleValuation g i (tripleTarget s g h i) = 1 := by
    simpa [tripleTarget,Targets.order] using mixedValue_value h (tripleEval s g i) (tripleValuation g i)
      p.val (tripleValuation_prime g i) none
  have hv : tripleValuation g i (tripleTarget s g h i) = tripleValuation g i 1 := he.trans (map_one _).symm
  rw [← norm_one (α := g.Field i)]
  exact le_antisymm (le_of_not_gt fun hgt => hv.not_gt ((tripleValuation_compat g i _ _).2 hgt))
    (le_of_not_gt fun hgt => hv.not_lt ((tripleValuation_compat g i _ _).2 hgt))

def triplePrecision (n : ℕ) (p : PrimeIndex) : ℝ := ‖(p.val : ℚ_[p.val])‖ ^ Targets.precision (Targets.generator n)

def wordLocal (h : History r M n) (w : BoundedWord n) : LocalPoly r p :=
  MvPolynomial.map (algebraMap ℚ ℚ_[p.val]) (wordDen h w)

def tripleTests (h : History r M n) (N : ℕ) (f : LocalPoly r p) : Prop :=
  s.TripleTests g n (oldDenominator h) (tripleTarget s g h) (triplePrecision n p)
    (wordLocal h) (fun w : BoundedWord n => w.latestExponent) N f

/-- The local coefficient choice depends only on the completed earlier rounds. -/
theorem tripleChoice (h : History r M n) (d : ℕ) (hd : s.tripleFloor g n ≤ d)
    (leading : LocalPoly r p) (hL : leading.totalDegree ≤ d) :
    ∃ L : OpenLower r d p, ∃ N : ℕ, ∀ q : LocalPoly r p, q.totalDegree < d →
      (fun m => q.coeff m) ∈ L.neighborhood → tripleTests s g h N (leading + q) := by
  have hH (i : Option Bool) (w : BoundedWord n) : aeval (s.triple g i) (wordLocal (p := p) h w) ≠ 0 := by
    rw [wordLocal,aeval_map_algebraMap]
    exact fun hz => wordDen_ne_zero h w ((s.triple_independent g i) (hz.trans (map_zero _).symm))
  exact s.triple_open g n d hd leading hL (oldDenominator h) (oldDenominator_ne_zero h)
    (tripleTarget s g h) (tripleTarget_norm s g h) (triplePrecision n p)
    (pow_pos (norm_pos_iff.mpr (Nat.cast_ne_zero.mpr p.property.ne_zero)) _)
    (wordLocal h) (fun w : BoundedWord n => w.latestExponent) (fun w => w.latestExponent_bounds.1) hH

theorem tripleTests_units (h : History r M n) {N : ℕ} {f : LocalPoly r p}
    (H : tripleTests s g h N f) (b : Bool) :
    ‖aeval (s.point b) f / aeval (s.point b) (oldDenominator h)‖ = 1 :=
  (H.values (some b)).1

end UnconditionalCounterexample.Variations.PrivateGuards.Live
