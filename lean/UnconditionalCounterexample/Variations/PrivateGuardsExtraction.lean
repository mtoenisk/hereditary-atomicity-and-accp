import UnconditionalCounterexample.Variations.PrivateGuardsMoving
import UnconditionalCounterexample.Variations.PrivateGuardsConductorWords
import UnconditionalCounterexample.Variations.MultiDomainLowExtraction

/-! # Extracting cofinally many mixed stage words from a non-BF subring -/

noncomputable section
namespace UnconditionalCounterexample.Variations.PrivateGuards.Live

open GuardSupport MultivariateSelection MultiDomain NormalizedWords PrimaryWordProfiles PrincipalProfiles
  StageExponents RawWords IntersectionDomain DiscreteOrders WithZero

variable {r d : ℕ} {c : Fin (r+1) → ℚ} {M : ℕ → Type*} (C : Config r d) (L : Rule r M c)
variable (π : ℕ → Valuation (FunctionField (r+1)) ℤᵐ⁰) (γ : PrimeIndex → Valuation (FunctionField (r+1)) ℤᵐ⁰)
local notation "D" => domain C L π γ
local notation "U" => normalizedMainValue C L

theorem mixed_words_of_profiles {I : Type*} (P : ValuationProfiles (D) I)
    (hs : ∀ x : D, IsUnit x → x = 1 ∨ x = -1)
    (hw : ∀ x : D, x ≠ 0 → P.value .limit x = 0 → (∀ i, P.value (.outside i) x = 0) →
      ∃ e : ℕ →₀ ℤ, ((x : FunctionField (r+1)) = word (U) e ∨ (x : FunctionField (r+1)) = -word (U) e) ∧
        Represents (bExponents e) (qExponents e) (fun j ↦ (P.value (.primary j) x : ℤ)))
    (T : Subring (D)) (hT : ¬ Factorization.IsBFDomain T) :
    HasMixedWords C L (T.map (IntersectionDomain.inclusion (horizontal C L).toSubring (branchVal C L π γ))) := by
  classical
  unfold Factorization.IsBFDomain at hT
  push Not at hT
  obtain ⟨x,hx,hlen⟩ := hT
  obtain ⟨k,_,hesc⟩ := P.exists_escaping_primary_divisors T (UnitSigns.subring_reflects_units hs T) hx hlen
  refine ⟨2*k,Set.infinite_of_forall_exists_gt ?_⟩
  intro N
  obtain ⟨z,hz⟩ := hesc (2*max N (2*k)+2)
  obtain ⟨e,he,hrep⟩ := hw z (fun h ↦ hz.ne_zero (Subtype.ext h)) hz.limit_zero hz.outside_zero
  let g (j : ℕ) : ℤ := P.value (.primary j) z
  obtain ⟨j,hj⟩ := hz.nonempty_support
  obtain ⟨n,hn,w,hwo,hl,ht,hb,_⟩ := exists_bounded_listed_word_beyond e g hrep k N
    (fun j ↦ ⟨Int.natCast_nonneg _, Int.ofNat_le.mpr (hz.primary_bound j)⟩)
    ⟨j,by dsimp [g]; exact_mod_cast hj.ne'⟩ (fun j h ↦ by simp [g,hz.prefix_zero j h])
  have heq := prod_eq_listed_word (U) e n (n+1) w hwo hl ht
  let ι := IntersectionDomain.inclusion (horizontal C L).toSubring (branchVal C L π γ)
  refine ⟨n,⟨w,hb,?_⟩,hn⟩
  rcases he with he | he
  · exact ⟨ι (z : D),⟨(z : D),z.property,rfl⟩,he.trans heq⟩
  · refine ⟨ι (-(z : D)),⟨-(z : D),(T.neg_mem z.property),rfl⟩,?_⟩
    change -((z : D) : FunctionField (r+1)) = _
    rw [he,neg_neg]
    exact heq

end UnconditionalCounterexample.Variations.PrivateGuards.Live
