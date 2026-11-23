import UnconditionalCounterexample.Variations.PrivateGuardsEvaluated
import UnconditionalCounterexample.Variations.MultiDomainPlaces

/-! # Moving returns in the common function field of a punctured history -/

noncomputable section
namespace UnconditionalCounterexample.Variations.PrivateGuards.Live

open GuardSupport MvPolynomial MultivariateSelection MultiDomain WithZero Filter NormalizedWords

variable {r d : ℕ} {M : ℕ → Type*} {c : Fin (r+1) → ℚ} {E : Type*} [Field E]
  (C : Config r d) (R : Rule r M c)

abbrev mixedMoving : ℕ → FunctionField (r+1) :=
  Targets.moving (coordinate 0) ((family C R).generator mixedPower)

variable (ψ : FunctionField (r+1) →+* E) (φ : Poly r →+* E)
  (hφ : ∀ f, ψ (algebraMap (Poly r) (FunctionField (r+1)) f) = φ f)

include hφ

theorem map_mixed_generator (n : ℕ) :
    ψ ((family C R).generator mixedPower n) = evaluated C R φ n := by
  unfold evaluated Family.generator normalizedMain
  simp only [map_div₀,map_prod,map_pow,map_mul,Function.comp_apply,hφ]
  rfl

theorem map_mixed_moving (n : ℕ) :
    ψ (mixedMoving C R n) = Targets.moving (φ (X 0)) (evaluated C R φ) n := by
  induction n with
  | zero => exact hφ _
  | succ n ih =>
    change ψ (mixedMoving C R n * _ / _) = Targets.moving _ _ n * _ / _
    rw [map_div₀,map_mul,ih,map_mixed_generator C R ψ φ hφ,map_mixed_generator C R ψ φ hφ]

theorem evaluated_evidence (v : Valuation E ℤᵐ⁰) (p : ℕ) (hp : v (p : E) = exp (-1))
    (label : Option ℕ) (n : ℕ)
    (h : φ (main C R n) ∈ mixedSet (before C R n) φ v p label) :
    (v.comap ψ) ((family C R).generator mixedPower n) =
      exp (-(Targets.order (Targets.generator n) label : ℤ)) ∧
    v ((Targets.target v p (Targets.order (Targets.generator n) label)
      (Targets.previous (φ (X 0)) (evaluated C R φ) (Targets.generator n)) / evaluated C R φ n - 1) /
      (p : E)^(Targets.precision (Targets.generator n))) ≤ 1 := by
  have hD : φ (oldDenominator (before C R n)) ≠ 0 := by
    rw [← hφ]
    intro hz
    apply oldDenominator_ne_zero (before C R n)
    apply IsFractionRing.injective (Poly r) (FunctionField (r+1))
    apply ψ.injective
    simpa using hz
  obtain ⟨hv,hr⟩ := evaluated_of_mem C R φ n v p hp label hD h
  exact ⟨(congrArg v (map_mixed_generator C R ψ φ hφ n)).trans hv,hr⟩

theorem field_moving_return (v : Valuation E ℤᵐ⁰) (p : ℕ) (hp : v (p : E) = exp (-1))
    (label : Option ℕ) (ht : (v.comap ψ) (coordinate (r := r+1) 0) = exp (-Targets.seedOrder label))
    (hv : ∀ n, (v.comap ψ) ((family C R).generator mixedPower n) = exp (-(Targets.order (Targets.generator n) label : ℤ)))
    (hmem : ∀ᶠ n in atTop, φ (main C R (Generator.q n).stage) ∈ mixedSet
      (before C R (Generator.q n).stage) φ v p label) :
    ∀ᶠ n in atTop, (v.comap ψ) ((mixedMoving C R n - 1) / (p : FunctionField (r+1))^n) ≤ 1 := by
  have ht' : v (φ (X 0)) = exp (-Targets.seedOrder label) := (congrArg v (hφ (X 0))).symm.trans ht
  have hv' n : v (evaluated C R φ n) = _ := (congrArg v (map_mixed_generator C R ψ φ hφ n)).symm.trans (hv n)
  have he := moving_return C R φ v p label ht' hv' (by
    filter_upwards [hmem] with n hn
    simpa only [Targets.generator_stage,Targets.precision] using
      (evaluated_evidence C R ψ φ hφ v p hp label _ hn).2)
  filter_upwards [he] with n hn
  change v (ψ _) ≤ 1
  rw [map_div₀,map_sub,map_one,map_pow,map_natCast,map_mixed_moving C R ψ φ hφ]
  exact hn

end UnconditionalCounterexample.Variations.PrivateGuards.Live
