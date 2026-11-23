import UnconditionalCounterexample.Variations.PrivateGuardsCoordinates
import UnconditionalCounterexample.Variations.PrivateGuardsMoving
import UnconditionalCounterexample.Variations.PrivateGuardsTablePermanence
import UnconditionalCounterexample.UnitSigns

/-! # Signed valuation profiles in the punctured domain

Vanishing of all outside orders includes both places of each private
pair. Their difference removes auxiliary exponents from a horizontal unit.
The remaining signed main word gives the congruences on primary exponents.
-/

noncomputable section
namespace UnconditionalCounterexample.Variations.PrivateGuards.Live

open GuardSupport WithZero DiscreteOrders PrincipalProfiles PrimaryWordProfiles NormalizedWords Filter
open MultivariateSelection

variable {r d : ℕ} {M : ℕ → Type*} {c : Fin (r+1) → ℚ} (C : Config r d) (L : Rule r M c)
local notation "K" => FunctionField (r+1)
variable (π : ℕ → Valuation (FunctionField (r+1)) ℤᵐ⁰) (γ : PrimeIndex → Valuation (FunctionField (r+1)) ℤᵐ⁰)
local notation "A" => mergedData C L π γ
local notation "V" => coordinateVal C L π γ
local notation "D" => domain C L π γ
local notation "U" => normalizedMainValue C L

/-- All main polynomials and punctures of the actual table retain the first-coordinate prime. -/
theorem table_retained {k : Type*} [Field k] [CharZero k] (P : TablePolicy r k) (q : PrimeIndex) :
    ∀ i, ¬ MultiDomain.TPoly r ∣ (mergedData C (tableRule P q c) π γ).raw i := by
  intro i
  change ¬ MultiDomain.TPoly r ∣ interleave _ _ i
  unfold interleave
  split
  · exact first_not_dvd_main P q c C _
  · exact first_not_dvd_puncture P q c C _

/-- Public specialization data together with the concrete private-pair schedule. -/
structure ProfileValues : Prop extends MovingValues C L π γ where
  retained : ∀ i, ¬ MultiDomain.TPoly r ∣ (mergedData C L π γ).raw i
  guard_above : ∀ p, γ p (p.val : K) < 1
  primary_late : ∀ x : K, x ≠ 0 → ∀ᶠ j in atTop, π j x = V .limit x
  guard_finite : ∀ x : K, x ≠ 0 → {p | γ p x ≠ 1}.Finite

namespace ProfileValues
variable {C L π γ} (H : ProfileValues C L π γ)

include H in
theorem signed_word {x : K} (hx : x ≠ 0)
    (hl : order (V .limit) x = 0) (ho : ∀ i, order (V (.outside i)) x = 0) :
    ∃ e : ℕ →₀ ℤ, (x = word U e ∨ x = -word U e) ∧
      Represents (StageExponents.bExponents e) (StageExponents.qExponents e) (fun j ↦ order (π j) x) := by
  obtain ⟨u,hu⟩ := MultiDomain.pole_unit_of_horizontal_zero A hx hl (fun p => ho (.inl (.inr p)))
  have hunit : ∃ u : (horizontal C L)ˣ, ((u : horizontal C L) : K) = x := by
    rw [← merged_pole C L π γ]; exact ⟨u,hu⟩
  obtain ⟨u,hu⟩ := hunit
  obtain ⟨e,he⟩ := pole_signed_main_word C L γ u (fun n => by
    rw [hu]; exact (ho (.inr (n,false))).trans (ho (.inr (n,true))).symm) H.guard_above
    (fun p => by rw [hu]; exact (order_eq_zero_iff _ hx).mp (ho (.inl (.inl p))))
    (fun p i => by simpa [branchVal,branchLabel,MultiDomain.Targets.order] using H.generator (.inl (.inr p)) i)
  rw [hu] at he
  refine ⟨e,he,represents_actual_primary_orders π U ?_ ?_ e x hx he⟩
  · intro n j
    simpa [branchVal,branchLabel] using H.generator (.inl (.inl j)) (Generator.b n).stage
  · intro n j
    simpa [branchVal,branchLabel] using H.generator (.inl (.inl j)) (Generator.q n).stage

include H in
theorem pure_triple {x : FunctionField (r+1)} (hx : x ≠ 0)
    (hl : order (V .limit) x = 0)
    (ho : ∀ i, order (V (.outside i)) x = 0) :
    TripleCongruent (fun j ↦ order (π j) x) := by
  obtain ⟨_, _, h⟩ := H.signed_word hx hl ho
  exact ValuationProfiles.tripleCongruent_of_represents h

include H in
theorem signs (x : D) (hx : IsUnit x) : x = 1 ∨ x = -1 := by
  have hzero (p) := order_eq_zero_of_isUnit (D) (V p)
    (fun z hz ↦ coordinate_integral C L π γ H.retained ⟨z, hz⟩ p) hx
  obtain ⟨e, he, hr⟩ := H.signed_word (x := (x : FunctionField (r+1)))
    (fun h ↦ hx.ne_zero (Subtype.ext h)) (hzero .limit) (fun i ↦ hzero (.outside i))
  have he0 := UnitSigns.exponents_eq_zero_of_represents_zero e _ hr (fun j ↦ hzero (.primary j))
  simp only [he0, word, Finsupp.prod_zero_index] at he
  exact he.imp Subtype.ext Subtype.ext

def profile : ValuationProfiles (D) (Outside C L π γ) where
  value p x := natOrder (V p) (x : FunctionField (r+1))
  value_unit p x hx := natOrder_eq_zero_of_isUnit _ _
    (fun z hz ↦ coordinate_integral C L π γ H.retained ⟨z,hz⟩ p) hx
  value_mul p x y hx hy := natOrder_mul _
    (fun h ↦ hx (Subtype.ext h)) (fun h ↦ hy (Subtype.ext h))
    (coordinate_integral C L π γ H.retained x p) (coordinate_integral C L π γ H.retained y p)
  unit_of_zero x hx hzero := by
    have ht : x ∣ 1 := (coordinate_dvd C L π γ H.retained x 1 hx one_ne_zero).mpr (fun p ↦ by
      rw [hzero]; exact Nat.zero_le _)
    exact isUnit_of_dvd_unit ht isUnit_one
  eventually_primary x hx := by
    obtain ⟨N,hN⟩ := eventually_atTop.mp (H.primary_late x (fun h ↦ hx (Subtype.ext h)))
    exact ⟨N, fun j hj ↦ congrArg (fun z : ℤᵐ⁰ ↦ (-z.log).toNat) (hN j hj)⟩
  finite_outside x hx := by
    have hn : (x : FunctionField (r+1)) ≠ 0 := fun h ↦ hx (Subtype.ext h)
    apply (finite_outside C L π γ hn (H.guard_finite x hn)).subset
    intro i hi hzero
    exact hi (congrArg Int.toNat hzero)
  pure_triple x hx hl ho := by
    have hn : (x : FunctionField (r+1)) ≠ 0 := fun h ↦ hx (Subtype.ext h)
    have hc (p) := natOrder_cast (V p) hn (coordinate_integral C L π γ H.retained x p)
    have ht : order (V .limit) x = 0 := by rw [← hc, hl]; rfl
    have hout (i) : order (V (.outside i)) x = 0 := by rw [← hc, ho]; rfl
    convert H.pure_triple hn ht hout using 1
    funext j
    exact hc (.primary j)

theorem profile_cast (p) {x : D} (hx : x ≠ 0) :
    (H.profile.value p x : ℤ) = order (V p) (x : FunctionField (r+1)) :=
  natOrder_cast _ (fun h ↦ hx (Subtype.ext h)) (coordinate_integral C L π γ H.retained x p)

theorem signedDifferenceTriple : H.profile.SignedDifferenceTriple := by
  intro x y hx hy hlx hly hout
  have hxn : (x : FunctionField (r+1)) ≠ 0 := fun h ↦ hx (Subtype.ext h)
  have hyn : (y : FunctionField (r+1)) ≠ 0 := fun h ↦ hy (Subtype.ext h)
  have hc (p) : order (V p) ((x : FunctionField (r+1)) / y) =
      (H.profile.value p x : ℤ) - H.profile.value p y := by
    rw [order_div _ hxn hyn, H.profile_cast _ hx, H.profile_cast _ hy]
  have hl : order (V .limit) ((x : FunctionField (r+1)) / y) = 0 := by simp [hc, hlx, hly]
  have ho (i) : order (V (.outside i)) ((x : FunctionField (r+1)) / y) = 0 := by
    rw [hc, hout, sub_self]
  convert H.pure_triple (div_ne_zero hxn hyn) hl ho using 1
  funext j
  exact (hc (.primary j)).symm

end ProfileValues
end UnconditionalCounterexample.Variations.PrivateGuards.Live
