import UnconditionalCounterexample.Variations.PrivateGuardsProfiles
import UnconditionalCounterexample.Variations.PrivateGuardsIntegerReturns
import UnconditionalCounterexample.Variations.PrivateGuardsExtraction
import UnconditionalCounterexample.Variations.PrivateGuardsCube

/-! # Hereditary atomicity for the punctured multivariate construction -/

noncomputable section
namespace UnconditionalCounterexample.Variations.PrivateGuards.Live.ProfileValues

open WithZero DiscreteOrders GuardSupport MultiDomain IntersectionDomain Filter

variable {r d : ℕ} {c : Fin (r+1) → ℚ} {M : ℕ → Type*} {C : Config r d} {L : Rule r M c}
variable {π : ℕ → Valuation (FunctionField (r+1)) ℤᵐ⁰} {γ : PrimeIndex → Valuation (FunctionField (r+1)) ℤᵐ⁰}
variable (H : ProfileValues C L π γ)

local notation "D" => domain C L π γ
local notation "K" => FunctionField (r+1)
local notation "A" => mergedData C L π γ
local notation "a" => movingElement C L π γ (ProfileValues.toMovingValues H)

include H in
theorem mixed_words (T : Subring (D)) (hT : ¬ Factorization.IsBFDomain T) :
    HasMixedWords C L (T.map (inclusion (horizontal C L).toSubring (branchVal C L π γ))) := by
  apply mixed_words_of_profiles C L π γ H.profile H.signs _ T hT
  intro z hz hl ho
  obtain ⟨e,he,hr⟩ := H.signed_word (x := (z : K)) (fun h ↦ hz (Subtype.ext h))
    (by rw [← H.profile_cast .limit hz,hl]; rfl)
    (fun i ↦ by rw [← H.profile_cast (.outside i) hz,ho]; rfl)
  exact ⟨e,he,(show (fun j ↦ order (π j) (z : K)) = (fun j ↦ (H.profile.value (.primary j) z : ℤ)) from
    funext fun j ↦ (H.profile_cast (.primary j) hz).symm) ▸ hr⟩

private theorem pole_integral {p : Polys (r+1)} (hp : Prime p) (hr : ∀ i, ¬p ∣ (mergedData C L π γ).raw i)
    (z : K) (hz : z ∈ horizontal C L) : PrimeOrders.valuation hp z ≤ 1 := by
  rw [← merged_pole C L π γ] at hz
  exact retained_integral (A) hp hr ⟨z,hz⟩

theorem moving_limit (n : ℕ) : H.profile.value .limit (a n) = 1 := by
  apply Int.ofNat_inj.mp
  rw [H.profile_cast _ (movingElement_ne C L π γ H.toMovingValues n)]
  let v := PrimeOrders.valuation (p := TPoly r) MvPolynomial.X_prime
  change -log (v (movingValue C L n)) = _
  rw [moving_horizontal C L v (pole_integral MvPolynomial.X_prime H.retained) n]
  change -log (PrimeOrders.valuation MvPolynomial.X_prime (algebraMap _ _ (TPoly r))) = _
  rw [PrimeOrders.valuation_self,log_exp]
  decide

theorem moving_outside (n i) : H.profile.value (.outside i) (a n) = 0 := by
  apply Int.ofNat_inj.mp
  rw [H.profile_cast _ (movingElement_ne C L π γ H.toMovingValues n)]
  apply (order_eq_zero_iff _ (show ((a n : D) : K) ≠ 0 from fun h ↦ movingElement_ne C L π γ H.toMovingValues n (Subtype.ext h))).mpr
  rcases i with (p | t) | ⟨k,b⟩
  · exact (moving_branch C L π γ H.toMovingValues (.inl (.inr p)) n).trans (by simp [branchLabel,Targets.movingOrder])
  · change t.val.valAt (movingValue C L n) = 1
    rw [moving_horizontal C L t.val.valAt (pole_integral t.val.prime t.val.retained) n]
    exact coordinate_other_first (A) t
  · cases b <;> exact (moving_branch C L π γ H.toMovingValues (.inr _) n).trans (by simp [branchLabel,Targets.movingOrder])

theorem moving_primary (n j) : (H.profile.value (.primary j) (a n) : ℤ) = primaryAtomProfile n j := by
  rw [H.profile_cast _ (movingElement_ne C L π γ H.toMovingValues n)]
  change -log (branchVal C L π γ (.inl (.inl j)) (movingValue C L n)) = _
  rw [moving_branch C L π γ H.toMovingValues,log_exp,neg_neg]
  rfl

theorem hereditarilyAtomic
    (hret : ∀ m : ℕ, 0 < m → ∀ᶠ n in atTop, (m : D) ∣ a n - 1)
    (hcond : ∀ T : Subring (D), HasMixedWords C L (T.map (inclusion (horizontal C L).toSubring (branchVal C L π γ))) →
      ∃ m : ℕ, 0 < m ∧ ∀ z : D, (m : D) * z ∈ T) : Factorization.IsHereditarilyAtomic (D) :=
  hereditarilyAtomic_of_profiles_and_integerConductors H.profile
    (fun x y hx hy ↦ (Live.coordinate_dvd C L π γ H.retained x y hx hy).mpr)
    H.signs (a) (movingElement_ne C L π γ H.toMovingValues) H.moving_limit H.moving_outside H.moving_primary
    (fun m hm N ↦ ((hret m hm).and (eventually_ge_atTop N)).exists.imp fun _ h ↦ ⟨h.2,h.1⟩)
    (fun T hT ↦ hcond T (H.mixed_words T hT))

end UnconditionalCounterexample.Variations.PrivateGuards.Live.ProfileValues
