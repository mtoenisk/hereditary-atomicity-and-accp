import UnconditionalCounterexample.Variations.DyadicRegularWords
import UnconditionalCounterexample.Variations.DyadicIntersections

/-!
# Escaping signed words in the literal dyadic intersection

The discrete orders give all supplementary and regular coordinates. Equal
signed profiles differ by a sign because their ratio is a unit of the
intersection. Hence individual scheduled regular columns and the two mass
equations yield the bounded-word sequence for an actual subring element with
unbounded factorization lengths.
-/

noncomputable section

namespace UnconditionalCounterexample.DyadicDeviations

open DiscreteOrders WithZero
open DyadicProfiles (Site)

variable {F G H : Type*} {J : Bool → Type*} [Field F]
variable (v : Site (Supplement J G H) → Valuation F ℤᵐ⁰) (signed : Fˣ → Profile J G H)
variable (hval : ∀ (u : Fˣ) i, (signed u).signedValues i = order (v i) (u : F))

include hval in
theorem signed_one_eq_zero : signed 1 = DyadicEscape.zeroProfile J G H := by
  apply Profile.signedValues_injective
  funext i
  rw [hval, Units.val_one, order_one]
  cases i with
  | centre _ | plus _ _ | minus _ _ => simp [DyadicEscape.zeroProfile, Profile.signedValues,
      Profile.plus, Profile.minus]
  | other j => cases j <;> rfl

include hval in
/-- Sign units of the intersection imply uniqueness up to sign in the entire
fraction field, even if neither function is integral. -/
theorem equal_up_to_sign_of_profile
    (hsign : ∀ z : fullIntersection v, IsUnit z → z = 1 ∨ z = -1)
    (a b : Fˣ) (h : signed a = signed b) : (a : F) = b ∨ (a : F) = -(b : F) := by
  have hzero (i : Site (Supplement J G H)) : order (v i) ((a : F) / (b : F)) = 0 := by
    rw [order_div (v i) a.ne_zero b.ne_zero, ← hval, ← hval, h, sub_self]
  have hn := div_ne_zero a.ne_zero b.ne_zero
  let z : fullIntersection v := ⟨(a:F)/(b:F), (IntersectionDomain.mem_intersection ⊤ v _).mpr
    ⟨Subring.mem_top _, fun i => (order_nonneg_iff (v i) hn).mp (hzero i).ge⟩⟩
  have hunit : IsUnit z := (isUnit_iff_order_zero v (fun he => hn (congrArg Subtype.val he))).mpr hzero
  rcases hsign z hunit with he | he
  · left
    have he' : (a:F)/(b:F) = 1 := congrArg Subtype.val he
    simpa using (div_eq_iff b.ne_zero).mp he'
  · right
    have he' : (a:F)/(b:F) = -1 := congrArg Subtype.val he
    simpa using (div_eq_iff b.ne_zero).mp he'

include hval in
/-- From one element with unbounded intrinsic decompositions, obtain an exact
bounded stage-word sequence in the same subring. No signed word factorizations
or escaping divisors are assumed. -/
theorem intersection_bounded_words
    (index : (k : Bool) → J k → ℕ) (sign : (k : Bool) → J k → ℤ)
    (hmass : ∀ u, (signed u).MassEquations index sign)
    (hlift : ∀ t : Profile J G H, t.MassEquations index sign → ∃ u, signed u = t)
    (hsign : ∀ z : fullIntersection v, IsUnit z → z = 1 ∨ z = -1)
    (s : DyadicEscape.Schedule) (W : ℕ → Fˣ)
    (hraw : ∀ g, signed (W (s.stage g)) =
      (signed 1).translate index sign (DyadicEscape.Generator.columns (Finsupp.single g 1)))
    (T : Subring (fullIntersection v)) {x : T} (hx : x ≠ 0)
    (hunbounded : ¬ Factorization.HasBoundedFactorizations x) :
    ∃ h : ℕ, ∃ y : ℕ → T, ∃ stage : ℕ → ℕ,
      ∃ w : ∀ i, RawWords.StageWord (stage i) (stage i+1),
        (∀ i, i < stage i) ∧ Filter.Tendsto stage Filter.atTop Filter.atTop ∧
        (∀ i, (w i).latestExponent ≤ h) ∧ (∀ i j, |(w i).oldExponent j| ≤ h) ∧
        ∀ i, ((y i : fullIntersection v) : F) = (W (stage i) : F) ^ (w i).latestExponent *
          ∏ j ∈ Finset.range (stage i), (W j : F) ^ (w i).oldExponent j := by
  let D := intersectionRealization v signed hval index sign hmass hlift
  refine D.exists_listed_sequence_of_unbounded (fullIntersection v).subtype
    (fun j => (W j : F)) s hsign ?_ T hx hunbounded
    (intersectionRealization_finite_extra v signed hval index sign hmass hlift x)
  intro a ha hh he
  have haF : (a : F) ≠ 0 := fun h => ha (Subtype.ext h)
  let u := Units.mk0 (a : F) haF
  have hr : D.regular a = (signed u).natRegular :=
    intersectionRealization_regular v signed hval index sign hmass hlift a haF
  have he' : (signed u).natExtra = 0 :=
    (intersectionRealization_extra v signed hval index sign hmass hlift a haF).symm.trans he
  have hn (i) : 0 ≤ (signed u).signedValues i := by
    rw [hval]
    exact (order_nonneg_iff (v i) haF).mpr (integral v a i)
  have hps : signed u = Profile.ofRegular (D.regular a) := by
    rw [hr]
    exact (signed u).eq_ofRegular_of_pure hn he'
  have hheight : (signed u).height = 0 := by
    funext k
    rw [hps]
    change ((D.regular a).height k : ℤ) = 0
    rw [hh k, Nat.cast_zero]
  obtain ⟨w, hw, hp, hm⟩ := DyadicEscape.exists_signed_word_of_pure s W signed index sign
    (signed_one_eq_zero v signed hval) hmass (equal_up_to_sign_of_profile v signed hval hsign)
    (fun g => column_multiplier_of_values v signed hval index sign _ _ (hraw g)) u hheight
    (by rw [hps]; rfl) (by rw [hps]; rfl) (by rw [hps]; rfl)
  refine ⟨w, hw, ?_, ?_⟩
  · intro k n
    rw [hp, hps]
    change ((D.regular a).height false : ℤ) +
      (((D.regular a).plus k n : ℤ) - (D.regular a).height false) = _
    omega
  · intro k n
    rw [hm, hps]
    change ((D.regular a).height true : ℤ) +
      (((D.regular a).minus k n : ℤ) - (D.regular a).height true) = _
    omega

end UnconditionalCounterexample.DyadicDeviations
