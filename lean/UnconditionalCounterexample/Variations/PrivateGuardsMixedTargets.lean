import UnconditionalCounterexample.Variations.PrivateGuardsLive
import UnconditionalCounterexample.Variations.MultiDomainStageTargets

/-!
# Mixed normalization and local arithmetic targets on actual finite histories

The very same auxiliary factors appearing in an earlier generator occur in
both the next evaluation target and the polynomial denominators of the word tests.
-/

noncomputable section
namespace UnconditionalCounterexample.Variations.PrivateGuards.Live

open MvPolynomial GuardSupport MultivariateSelection MultiDomain WithZero
open scoped Topology

variable {r n : ℕ} {M : ℕ → Type*} {L : Type*}

def prefixMain (h : History r M n) (i : ℕ) : Poly r :=
  if hi : i < n then (h ⟨i,hi⟩).entry.raw i else 1

def prefixPuncture (h : History r M n) (i : ℕ) : Poly r :=
  if hi : i < n then (h ⟨i,hi⟩).puncture else 1

theorem prefixMain_ne_zero (h : History r M n) (i : ℕ) : prefixMain h i ≠ 0 := by
  unfold prefixMain
  split <;> first | exact (h _).irreducible.ne_zero | exact one_ne_zero

theorem prefixPuncture_ne_zero (h : History r M n) (i : ℕ) : prefixPuncture h i ≠ 0 := by
  unfold prefixPuncture
  split <;> first | exact (h _).irreducible_puncture.ne_zero | exact one_ne_zero

def wordDen (h : History r M n) (w : BoundedWord n) : Poly r :=
  mixedDenominator (prefixMain h) (prefixPuncture h) w

theorem wordDen_ne_zero (h : History r M n) (w : BoundedWord n) : wordDen h w ≠ 0 := by
  unfold wordDen mixedDenominator MultivariateSelection.denominator
  apply Finset.prod_ne_zero_iff.mpr
  intro j _
  apply pow_ne_zero
  unfold interleave
  split <;> first | apply prefixMain_ne_zero | apply prefixPuncture_ne_zero

section
variable [Field L] (h : History r M n) (φ : Poly r →+* L)

def prefixNormalized : ℕ → L :=
  normalizedMain (φ ∘ prefixMain h) (φ ∘ prefixPuncture h) mixedPower

def mixedValue (v : Valuation L ℤᵐ⁰) (p : ℕ) (label : Option ℕ) : L :=
  Targets.target v p (Targets.order (Targets.generator n) label)
    (Targets.previous (φ (X 0)) (prefixNormalized h φ) (Targets.generator n))

def mixedRaw (v : Valuation L ℤᵐ⁰) (p : ℕ) (label : Option ℕ) : L :=
  φ (oldDenominator h) * mixedValue h φ v p label

def mixedSet (v : Valuation L ℤᵐ⁰) (p : ℕ) (label : Option ℕ) : Set L :=
  Targets.neighborhood v p (φ (oldDenominator h)) (mixedValue h φ v p label)
    (Targets.precision (Targets.generator n))

theorem mixedValue_value (v : Valuation L ℤᵐ⁰) (p : ℕ) (hp : v (p : L) = exp (-1))
    (label : Option ℕ) :
    v (mixedValue h φ v p label) = exp (-(Targets.order (Targets.generator n) label : ℤ)) :=
  Targets.target_value v p hp _ _

theorem mixedValue_ne_zero (v : Valuation L ℤᵐ⁰) (p : ℕ) (hp : v (p : L) = exp (-1))
    (label : Option ℕ) : mixedValue h φ v p label ≠ 0 := Targets.target_ne_zero v p hp _ _

theorem mixedRaw_ne_zero (v : Valuation L ℤᵐ⁰) (p : ℕ) (hp : v (p : L) = exp (-1))
    (label : Option ℕ) (hD : φ (oldDenominator h) ≠ 0) : mixedRaw h φ v p label ≠ 0 :=
  mul_ne_zero hD (mixedValue_ne_zero h φ v p hp label)

theorem mixedSet_return (v : Valuation L ℤᵐ⁰) (p : ℕ) (hp : v (p : L) = exp (-1))
    (label : Option ℕ) (hD : φ (oldDenominator h) ≠ 0) {x : L} (hx : x ∈ mixedSet h φ v p label) :
    let u := x / φ (oldDenominator h)
    v u = exp (-(Targets.order (Targets.generator n) label : ℤ)) ∧
    v ((mixedValue h φ v p label / u - 1) / (p : L)^(Targets.precision (Targets.generator n))) ≤ 1 := by
  have hv := Targets.normalized_and_return v p (v.ne_zero_iff.mp (hp ▸ exp_ne_zero))
    hD (mixedValue_ne_zero h φ v p hp label) _ hx
  exact ⟨hv.1.trans (mixedValue_value h φ v p hp label),hv.2⟩

end

theorem mixedSet_mem [NormedField L] (h : History r M n) (φ : Poly r →+* L)
    (v : Valuation L ℤᵐ⁰) (p : ℕ) (hp : v (p : L) = exp (-1))
    (compat : ∀ a b : L, v a < v b ↔ ‖a‖ < ‖b‖)
    (label : Option ℕ) (hD : φ (oldDenominator h) ≠ 0) :
    mixedSet h φ v p label ∈ 𝓝 (mixedRaw h φ v p label) :=
  Targets.neighborhood_mem_nhds v compat p (v.ne_zero_iff.mp (hp ▸ exp_ne_zero))
    hD (mixedValue_ne_zero h φ v p hp label) _

end UnconditionalCounterexample.Variations.PrivateGuards.Live
