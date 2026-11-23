import UnconditionalCounterexample.Variations.PrivateGuardsMoving

/-! # The literal strict chain at the first coordinate cubed in the punctured ring -/

noncomputable section
namespace UnconditionalCounterexample.Variations.PrivateGuards.Live

open GuardSupport MultivariateSelection IntersectionDomain WithZero MultiDomain NormalizedWords PrimaryWordProfiles

variable {r d : ℕ} {c : Fin (r+1) → ℚ} {M : ℕ → Type*} (C : Config r d) (L : Rule r M c)
local notation "K" => FunctionField (r+1)
local notation "U" => normalizedMainValue C L
variable (π : ℕ → Valuation (FunctionField (r+1)) ℤᵐ⁰) (γ : PrimeIndex → Valuation (FunctionField (r+1)) ℤᵐ⁰) (H : MovingValues C L π γ)
local notation "V" => branchVal C L π γ
local notation "D" => domain C L π γ

private def prefixProduct (n : ℕ) : K := ∏ j ∈ Finset.range n, U (Generator.b j).stage

private theorem prefixProduct_ne (n : ℕ) : prefixProduct C L n ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr (fun _ _ ↦ mixed_ne C L _)

def cubeTerm (n : ℕ) : K := coordinate 0 ^ 3 / prefixProduct C L n

include H in
theorem cubeTerm_mem (n : ℕ) : cubeTerm C L n ∈ D := by
  apply (div_mem_iff _ _ (prefixProduct_ne C L n)).mpr
  constructor
  · change coordinate 0 ^ 3 / prefixProduct C L n ∈ horizontal C L
    rw [div_eq_mul_inv,prefixProduct,← Finset.prod_inv_distrib]
    exact (horizontal C L).mul_mem ((horizontal C L).pow_mem ((horizontal C L).algebraMap_mem _) _)
      (Submonoid.prod_mem _ (fun _ _ ↦ mixed_inverse_mem C L _))
  · intro i
    rw [map_pow,prefixProduct,map_prod,H.seed]
    simp only [H.generator,Targets.generator_stage]
    cases hl : branchLabel i with
    | none => simp [Targets.seedOrder,Targets.order]
    | some j =>
      simp only [Targets.seedOrder,Targets.b_order]
      rw [prod_exp_neg,← exp_nsmul, exp_le_exp, nsmul_eq_mul]
      have h := PaperCubeChain.sum_bWeight_le_three (Finset.range n) j
      have ht : 1 ≤ primaryAtomProfile 0 j := by
        simp only [primaryAtomProfile]
        split_ifs <;> omega
      omega

include H in
theorem ratio_mem (n : ℕ) : U (Generator.b n).stage ∈ D := by
  apply (mem_intersection _ _ _).mpr
  refine ⟨mixed_mem C L _,fun i ↦ ?_⟩
  change (V) i (U _) ≤ 1
  rw [H.generator, exp_le_one_iff]
  exact neg_nonpos.mpr (Int.natCast_nonneg _)

def factor (n : ℕ) : D := ⟨_,ratio_mem C L π γ H n⟩

theorem factor_nonunit (n : ℕ) : ¬ IsUnit (factor C L π γ H n) := by
  rintro ⟨u,hu⟩
  have hv := unit_branch_value C L π γ u (.inl (.inl (2*n)))
  rw [hu] at hv
  change (V) (.inl (.inl (2*n))) (U (Generator.b n).stage) = 1 at hv
  rw [H.generator] at hv
  simp [branchLabel,Targets.generator_stage,Targets.b_order,bWeight] at hv

include H in
theorem cube_chain : ∃ t : D, (t : K) = coordinate 0 ∧ HasStrictChainAt (t^3) := by
  let v (n) : D := ⟨cubeTerm C L n,cubeTerm_mem C L π γ H n⟩
  have hne (n : ℕ) : v n ≠ 0 := by
    intro h
    exact (div_ne_zero (pow_ne_zero 3 ((map_ne_zero_iff _ (IsFractionRing.injective (Polys (r+1)) K)).mpr (MvPolynomial.X_ne_zero (0 : Fin (r+1))))) (prefixProduct_ne C L n)) (congrArg (domain C L π γ).subtype h)
  have hr (n : ℕ) : v n = v (n+1) * factor C L π γ H n := by
    apply Subtype.ext
    change coordinate 0 ^ 3 / prefixProduct C L n =
      coordinate 0 ^ 3 / prefixProduct C L (n+1) * U (Generator.b n).stage
    rw [show prefixProduct C L (n+1) = prefixProduct C L n * U (Generator.b n).stage from Finset.prod_range_succ ..]
    rw [div_mul_eq_div_div, div_mul_cancel₀ _ (mixed_ne C L _)]
  exact ⟨movingElement C L π γ H 0,rfl,v,Subtype.ext (by simp [v,cubeTerm,prefixProduct,movingElement,movingValue,Targets.moving]),
    hne, strictMono_principalIdeals_of_nonunit_recurrence v _ hne (factor_nonunit C L π γ H) hr⟩

end UnconditionalCounterexample.Variations.PrivateGuards.Live
