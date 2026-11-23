import UnconditionalCounterexample.Variations.MultiDomainEvaluated

/-!
# Images of the moving terms under evaluation of the pole algebra

A homomorphism out of the horizontal localization evaluates every normalized
unit as the corresponding quotient, and respects the entire moving recurrence.
-/

noncomputable section
namespace UnconditionalCounterexample.MultivariateSelection

open GuardSupport Variations MultiDomain NormalizedWords MvPolynomial

variable {K : Type*} [Field K] [CharZero K] [IsAlgClosed K] {r : ℕ} {q : PrimeIndex}
  (L : LocalPrescription r q) (G : Geometry r K)
variable {E : Type*} [Field E]

theorem pole_normalized (e : poleAlgebra (selectedData L G) →+* E) (n : ℕ) :
    e (selectedUnit L G n : poleAlgebra (selectedData L G)) =
      RawWords.normalizedFactor
        (fun j ↦ e (algebraMap _ (poleAlgebra (selectedData L G)) (siteRaw L G j))) normalizationPower n := by
  let A := selectedData L G
  let f := algebraMap (Polys (r+1)) (poleAlgebra A)
  let d := ∏ j ∈ Finset.range n, f (siteRaw L G j)^normalizationPower n
  have hraw (j : ℕ) : IsUnit (f (siteRaw L G j)) :=
    IsLocalization.map_units (poleAlgebra A) (⟨_,Submonoid.subset_closure (Set.mem_range_self j)⟩ : denominators A)
  have hden : (d : FunctionField (r+1)) ≠ 0 := fun h ↦
    (Finset.prod_ne_zero_iff.mpr fun j _ ↦ pow_ne_zero _ (hraw j).ne_zero) (Subtype.ext h : d = 0)
  have hh : (selectedUnit L G n : poleAlgebra A) * d = f (siteRaw L G n) := by
    apply Subtype.ext
    change (rawValue A n / (∏ j ∈ Finset.range n, rawValue A j^normalizationPower n)) * (d : FunctionField (r+1)) = _
    have he : (d : FunctionField (r+1)) = ∏ j ∈ Finset.range n, rawValue A j ^ normalizationPower n := by
      simp [d, f,rawValue,A]
      rfl
    rw [← he,div_mul_cancel₀ _ hden]
    rfl
  change e _ = e _ / _
  have he := congrArg e hh
  rw [map_mul] at he
  have hed : e d = ∏ j ∈ Finset.range n, e (f (siteRaw L G j)) ^ normalizationPower n := by simp [d]
  rw [eq_div_iff (Finset.prod_ne_zero_iff.mpr fun j _ ↦ pow_ne_zero _ ((hraw j).map e).ne_zero), ← hed]
  exact he

theorem pole_moving (V : VerticalProfiles (selectedData L G) normalizationPower)
    (hr : ∀ n, ¬ TPoly r ∣ siteRaw L G n) (e : poleAlgebra (selectedData L G) →+* E) (n : ℕ) :
    let C := selectedProfileChoices L G hr V
    e (C.movingPole n) = Targets.moving (e (algebraMap _ _ (X 0 : Polys (r+1))))
      (RawWords.normalizedFactor (fun j ↦ e (algebraMap _ _ (siteRaw L G j))) normalizationPower) n := by
  let C := selectedProfileChoices L G hr V
  induction n with
  | zero => simp [MovingData.movingPole,MovingData.multiplier,Targets.moving]
  | succ n ih =>
    have h : C.movingPole (n+1) * (C.qRatio n : poleAlgebra (selectedData L G)) =
        C.movingPole n * (C.b (n+1) : poleAlgebra (selectedData L G)) := by
      apply Subtype.ext
      change (C.movingPole (n+1) : FunctionField (r+1)) * _ = _
      rw [C.movingPole_succ,div_mul_cancel₀ _ (fun h ↦ (C.qRatio n).ne_zero (Subtype.ext h))]
      rfl
    have he := congrArg e h
    rw [map_mul,map_mul] at he
    change e _ = _ * _ / _
    rw [← pole_normalized L G e (Generator.q n).stage, ← pole_normalized L G e (Generator.b (n+1)).stage,
      eq_div_iff (((selectedUnit L G (Generator.q n).stage).isUnit.map e).ne_zero), ← ih]
    exact he

end UnconditionalCounterexample.MultivariateSelection
