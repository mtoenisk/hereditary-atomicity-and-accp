import UnconditionalCounterexample.Variations.DyadicBaseLifts
import UnconditionalCounterexample.HorizontalOrders
import UnconditionalCounterexample.PairedResidues

/-!
# Coarse dyadic profiles of rational functions

A retained monic irreducible produces its singleton horizontal order. A
rational prime produces its singleton guard order with zero horizontal
profile, including at centres. Thus arbitrary finite horizontal and guard
targets require no further polynomial selections.
-/

noncomputable section
namespace UnconditionalCounterexample.DyadicDeviations
open DiscreteOrders WithZero
open DyadicProfiles (Site)
open PrincipalProfiles (MonicIrreducible)

variable {J : Bool → Type*} {G H : Type*}
    (v : Site (Supplement J G H) → Valuation (RatFunc ℚ) ℤᵐ⁰)
    (signed : (RatFunc ℚ)ˣ → Profile J G H)
    (hval : ∀ (u : (RatFunc ℚ)ˣ) i, (signed u).signedValues i = order (v i) (u : RatFunc ℚ))
    (horizontal : HorizontalIndex H → MonicIrreducible ℚ) (hinj : Function.Injective horizontal)
    (hhor : ∀ i, v (horizontalSite i) = HorizontalOrders.valuation (horizontal i))

include hval hinj hhor in
theorem exists_horizontal_single (i : HorizontalIndex H) :
    ∃ u, (signed u).horizontalPart = Finsupp.single i 1 := by
  classical
  let u := Units.mk0 _ (PrincipalProfiles.factor_ne_zero (horizontal i))
  refine ⟨u, Finsupp.ext fun j => ?_⟩
  rw [Profile.horizontalPart_apply, hval, hhor]
  change order (HorizontalOrders.valuation (horizontal j)) (PrincipalProfiles.factor (horizontal i)) = _
  by_cases h : i = j
  · subst j
    simp [order]
  · simp [order, HorizontalOrders.valuation_factor_of_ne _ _ (fun he => h (hinj he)),
      Finsupp.single_eq_of_ne (Ne.symm h)]

variable (prime : GuardIndex J G → {p : ℕ // p.Prime}) (pinj : Function.Injective prime)
    (guard : (i : GuardIndex J G) → RatFunc ℚ →+* ℚ_[(prime i).val])
    (hguard : ∀ i, v (guardSite i) =
      @EvaluationDVR.valuation (prime i).val ⟨(prime i).property⟩ _ _ (guard i))

include hval hhor pinj hguard in
theorem exists_guard_single (i : GuardIndex J G) :
    ∃ u, (signed u).horizontalPart = 0 ∧ (signed u).guardPart = Finsupp.single i 1 := by
  classical
  let p := (prime i).val
  have hp : p.Prime := (prime i).property
  let : Fact p.Prime := ⟨hp⟩
  have hn : (p : RatFunc ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  let u := Units.mk0 (p : RatFunc ℚ) hn
  refine ⟨u, Finsupp.ext fun j => ?_, Finsupp.ext fun j => ?_⟩
  · rw [Profile.horizontalPart_apply, hval, hhor]
    change order (HorizontalOrders.valuation (horizontal j)) (p : RatFunc ℚ) = 0
    have hC : (p : RatFunc ℚ) = RatFunc.C (p : ℚ) := (map_natCast _ _).symm
    rw [hC, order, HorizontalOrders.valuation_constant _ _ (Nat.cast_ne_zero.mpr hp.ne_zero)]
    simp
  · rw [Profile.guardPart_apply, hval, hguard]
    by_cases he : i = j
    · subst j
      change order (EvaluationDVR.valuation p (guard i)) (p : RatFunc ℚ) = _
      simp [order]
    · let q := (prime j).val
      let : Fact q.Prime := ⟨(prime j).property⟩
      have hne : p ≠ q := fun heq => he (pinj (Subtype.ext heq))
      change order (EvaluationDVR.valuation q (guard j)) (p : RatFunc ℚ) = _
      simp [order, PairedResidues.valuation_prime_eq_one_of_ne p q (guard j) hne,
        Finsupp.single_eq_of_ne (Ne.symm he)]

include hval hinj hhor pinj hguard in
/-- The horizontal/guard lift required by signed column elimination in the
actual rational function field. -/
theorem exists_rational_base_lift (t : Profile J G H) :
    ∃ b, (signed b).height = t.height ∧ (signed b).guards = t.guards ∧
      (signed b).horizontal = t.horizontal :=
  exists_horizontal_guard_lift v signed hval
    (exists_horizontal_single v signed hval horizontal hinj hhor)
    (exists_guard_single v signed hval horizontal hhor prime pinj guard hguard) t

end UnconditionalCounterexample.DyadicDeviations
