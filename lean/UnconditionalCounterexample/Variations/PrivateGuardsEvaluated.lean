import UnconditionalCounterexample.Variations.PrivateGuardsMixedTargets
import UnconditionalCounterexample.Variations.PrivateGuardsRealized
import UnconditionalCounterexample.Variations.MultiDomainLocalReturns

/-! # The normalized values and returns on the actual simultaneous history -/

noncomputable section
namespace UnconditionalCounterexample.Variations.PrivateGuards.Live

open MvPolynomial GuardSupport MultivariateSelection MultiDomain NormalizedWords WithZero Filter

variable {r d : ℕ} {M : ℕ → Type*} {c : Fin (r+1) → ℚ} {E : Type*} [Field E]
  (C : Config r d) (R : Rule r M c) (φ : Poly r →+* E)

def evaluated : ℕ → E :=
  normalizedMain (φ ∘ main C R) (φ ∘ puncture C R) mixedPower

theorem evaluated_eq (n : ℕ) :
    evaluated C R φ n = φ (main C R n) / φ (oldDenominator (before C R n)) := by
  unfold evaluated normalizedMain oldDenominator
  simp only [Function.comp_apply,map_prod,map_pow,map_mul]
  congr 1
  exact (Fin.prod_univ_eq_prod_range (fun j =>
    (φ (main C R j) * φ (puncture C R j)) ^ mixedPower n) n).symm

theorem prefixNormalized_eq {i n : ℕ} (hi : i < n) :
    prefixNormalized (before C R n) φ i = evaluated C R φ i := by
  unfold prefixNormalized evaluated normalizedMain
  simp only [Function.comp_apply,prefixMain,dite_eq_left hi]
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  have hjn := (Finset.mem_range.mp hj).trans hi
  simp only [prefixPuncture,dite_eq_left hjn,before,main,puncture]

theorem mixedValue_eq (n : ℕ) (v : Valuation E ℤᵐ⁰) (p : ℕ) (label : Option ℕ) :
    mixedValue (before C R n) φ v p label = Targets.target v p (Targets.order (Targets.generator n) label)
      (Targets.previous (φ (X 0)) (evaluated C R φ) (Targets.generator n)) := by
  unfold mixedValue
  apply congrArg (Targets.target v p _)
  apply Targets.previous_congr
  rw [Targets.stage_generator]
  exact fun _ hi => prefixNormalized_eq C R φ hi

/-- At a site processed in this round the valuation and the relative return
hold for the actual normalized mixed generator. -/
theorem evaluated_of_mem (n : ℕ) (v : Valuation E ℤᵐ⁰) (p : ℕ) (hp : v (p : E) = exp (-1))
    (label : Option ℕ) (hD : φ (oldDenominator (before C R n)) ≠ 0)
    (h : φ (main C R n) ∈ mixedSet (before C R n) φ v p label) :
    v (evaluated C R φ n) = exp (-(Targets.order (Targets.generator n) label : ℤ)) ∧
    v ((Targets.target v p (Targets.order (Targets.generator n) label)
      (Targets.previous (φ (X 0)) (evaluated C R φ) (Targets.generator n)) / evaluated C R φ n - 1) /
      (p : E)^(Targets.precision (Targets.generator n))) ≤ 1 := by
  have hv := mixedSet_return (before C R n) φ v p hp label hD h
  dsimp only at hv
  rw [← evaluated_eq, mixedValue_eq] at hv
  exact hv

/-- Applied to the stage evidence above, the q-stage congruences give
integer returns of the moving sequence on the same local branch. -/
theorem moving_return (v : Valuation E ℤᵐ⁰) (p : ℕ) (label : Option ℕ)
    (ht : v (φ (X 0)) = exp (-Targets.seedOrder label))
    (hv : ∀ n, v (evaluated C R φ n) = exp (-(Targets.order (Targets.generator n) label : ℤ)))
    (hq : ∀ᶠ n in atTop, v ((Targets.target v p (Targets.order (.q n) label)
      (Targets.previous (φ (X 0)) (evaluated C R φ) (.q n)) / evaluated C R φ (Generator.q n).stage - 1) /
      (p : E)^(n+1)) ≤ 1) :
    ∀ᶠ n in atTop, v ((Targets.moving (φ (X 0)) (evaluated C R φ) n - 1) / (p : E)^n) ≤ 1 := by
  obtain ⟨N,hN⟩ := eventually_atTop.mp ((Targets.eventually_refined v _ _ label ht hv).and hq)
  refine eventually_atTop.mpr ⟨N+1,fun k hk => ?_⟩
  obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show k ≠ 0 by omega)
  obtain ⟨⟨ho,hu⟩,h⟩ := hN n (by omega)
  unfold Targets.target at h
  rw [ite_eq_left ⟨ho,hu⟩] at h
  exact h

end UnconditionalCounterexample.Variations.PrivateGuards.Live
