import UnconditionalCounterexample.Variations.MultiDomainTargets
import UnconditionalCounterexample.Variations.MultivariateSelectionWords

/-!
# Arithmetic targets on a chronological multivariate prefix

All denominators and return numerators are evaluated on the earlier
polynomials of the selector's actual history. The resulting value and its
open neighbourhood apply to each component of its finite local input.
-/

noncomputable section
namespace UnconditionalCounterexample.Variations.MultiDomain.Targets

open MultivariateSelection NormalizedWords WithZero
open scoped Topology

variable {r n : ℕ} {M : ℕ → Type*} {L : Type*} [Field L]

def prefixValue (h : History r M n) (f : Polys (r+1) →+* L) (i : ℕ) : L :=
  if hi : i<n then f ((h ⟨i,hi⟩).raw i) else 1

def denominator (P : ℕ → L) (n : ℕ) : L := ∏ j ∈ Finset.range n, P j ^ normalizationPower n

def precision : Generator → ℕ
  | .b _ => 1
  | .q k => k+1

def stageValue (v : Valuation L ℤᵐ⁰) (p : ℕ) (label : Option ℕ) (t : L) (P : ℕ → L) (n : ℕ) : L :=
  target v p (order (generator n) label) (previous t (RawWords.normalizedFactor P normalizationPower) (generator n))

def rawTarget (h : History r M n) (f : Polys (r+1) →+* L)
    (v : Valuation L ℤᵐ⁰) (p : ℕ) (label : Option ℕ) : L :=
  denominator (prefixValue h f) n * stageValue v p label (f (MvPolynomial.X 0)) (prefixValue h f) n

def rawNeighborhood (h : History r M n) (f : Polys (r+1) →+* L)
    (v : Valuation L ℤᵐ⁰) (p : ℕ) (label : Option ℕ) : Set L :=
  neighborhood v p (denominator (prefixValue h f) n)
    (stageValue v p label (f (MvPolynomial.X 0)) (prefixValue h f) n) (precision (generator n))

private theorem prefixDen_ne (h : History r M n) (f : Polys (r+1) →+* L)
    (hF : ∀ i : Fin n, f ((h i).raw i.val) ≠ 0) : denominator (prefixValue h f) n ≠ 0 := by
  classical
  apply Finset.prod_ne_zero_iff.mpr
  intro i hi
  exact pow_ne_zero _ (by simpa only [prefixValue, dite_eq_left (Finset.mem_range.mp hi)] using hF ⟨i,Finset.mem_range.mp hi⟩)

theorem rawTarget_ne_zero (h : History r M n) (f : Polys (r+1) →+* L)
    (v : Valuation L ℤᵐ⁰) (p : ℕ) (label : Option ℕ) (hp : v (p : L) = exp (-1))
    (hF : ∀ i : Fin n, f ((h i).raw i.val) ≠ 0) : rawTarget h f v p label ≠ 0 :=
  mul_ne_zero (prefixDen_ne h f hF) (target_ne_zero v p hp _ _)

theorem rawNeighborhood_mem {L : Type*} [NormedField L] (h : History r M n) (f : Polys (r+1) →+* L)
    (v : Valuation L ℤᵐ⁰) (p : ℕ) (label : Option ℕ) (hp : v (p : L) = exp (-1))
    (compat : ∀ a b : L, v a < v b ↔ ‖a‖ < ‖b‖)
    (hF : ∀ i : Fin n, f ((h i).raw i.val) ≠ 0) :
    rawNeighborhood h f v p label ∈ 𝓝 (rawTarget h f v p label) :=
  neighborhood_mem_nhds v compat p (v.ne_zero_iff.mp (hp ▸ exp_ne_zero))
    (prefixDen_ne h f hF) (target_ne_zero v p hp _ _) _

theorem denominator_congr {P Q : ℕ → L} (n : ℕ) (h : ∀ j<n, P j = Q j) :
    denominator P n = denominator Q n :=
  Finset.prod_congr rfl fun j hj ↦ congrArg (· ^ normalizationPower n) (h j (Finset.mem_range.mp hj))

theorem stageValue_congr (v : Valuation L ℤᵐ⁰) (p : ℕ) (label : Option ℕ) (t : L) {P Q : ℕ → L}
    (n : ℕ) (h : ∀ j<n, P j = Q j) : stageValue v p label t P n = stageValue v p label t Q n := by
  unfold stageValue
  apply congrArg (target v p _)
  apply previous_congr
  rw [stage_generator]
  intro j hj
  exact congrArg₂ (· / ·) (h j hj) (denominator_congr j fun i hi ↦ h i (hi.trans hj))

variable {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]

/-- Local evidence at the selected stage determines both the valuation of
its literal normalized factor and the relative congruence of that factor. -/
theorem actual_normalized (R : Requirements r M K) (f : Polys (r+1) →+* L)
    (v : Valuation L ℤᵐ⁰) (p : ℕ) (label : Option ℕ) (hp : v (p : L) = exp (-1))
    (hF : ∀ j, f (raw R j) ≠ 0) (n : ℕ)
    (h : f (raw R n) ∈ rawNeighborhood (fun i : Fin n ↦ chain R i.val) f v p label) :
    let P := fun i ↦ f (raw R i)
    let U := RawWords.normalizedFactor P normalizationPower
    v (U n) = exp (-(order (generator n) label : ℤ)) ∧
      v ((stageValue v p label (f (MvPolynomial.X 0)) P n / U n - 1) / (p : L)^precision (generator n)) ≤ 1 := by
  let P := fun i ↦ f (raw R i)
  let h' := fun i : Fin n ↦ chain R i.val
  have he (i : ℕ) (hi : i<n) : prefixValue h' f i = P i := by simp [prefixValue,hi,h',P,raw]
  have hr := normalized_and_return v p (v.ne_zero_iff.mp (hp ▸ exp_ne_zero))
    (prefixDen_ne h' f fun i ↦ hF i.val) (target_ne_zero v p hp _ _) _ h
  let y := stageValue v p label (f (MvPolynomial.X 0)) (prefixValue h' f) n
  change v (P n / denominator (prefixValue h' f) n) = v y ∧
    v ((y / (P n / denominator (prefixValue h' f) n) - 1) / (p : L)^precision (generator n)) ≤ 1 at hr
  dsimp only [y] at hr
  rw [denominator_congr n he, stageValue_congr v p label _ n he] at hr
  exact ⟨hr.1.trans (target_value v p hp _ _), hr.2⟩

end UnconditionalCounterexample.Variations.MultiDomain.Targets
