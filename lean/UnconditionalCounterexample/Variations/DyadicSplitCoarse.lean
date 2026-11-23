import UnconditionalCounterexample.Variations.DyadicSplitPrefix
import UnconditionalCounterexample.Variations.DyadicRationalLifts

/-!
# Explicit horizontal and scalar factors for a dyadic split

The field element recorded at round opening is computed as a product of
retained irreducibles times scalar prime powers and a sign. Only guards
whose prescribed order differs from the horizontal product's order need
scalar corrections.
-/

noncomputable section
namespace UnconditionalCounterexample.DyadicSplit

open DiscreteOrders WithZero DyadicDeviations
open PrincipalProfiles (MonicIrreducible)
open DyadicProfiles (Site)

variable {J : Bool → Type*} {G H : Type*}

/-- The monic factor in the rational function field itself. -/
def horizontalUnit (f : MonicIrreducible ℚ) : (RatFunc ℚ)ˣ :=
  Units.mk0 (PrincipalProfiles.factor f) (PrincipalProfiles.factor_ne_zero f)

private theorem weighted_single {I : Type*} [DecidableEq I] (e : I →₀ ℤ) (i : I) :
    (e.sum fun j z => z * (if j = i then 1 else 0)) = e i := by
  classical
  by_cases hi : i ∈ e.support <;> simp [Finsupp.sum, mul_ite, hi, Finsupp.notMem_support_iff.mp]

variable (v : Site (Supplement J G H) → Valuation (RatFunc ℚ) ℤᵐ⁰)
    (signed : (RatFunc ℚ)ˣ → Profile J G H)
    (hval : ∀ (u : (RatFunc ℚ)ˣ) i, (signed u).signedValues i = order (v i) (u : RatFunc ℚ))
    (horizontal : HorizontalIndex H → MonicIrreducible ℚ) (hinj : Function.Injective horizontal)
    (hhor : ∀ i, v (horizontalSite i) = HorizontalOrders.valuation (horizontal i))
    (prime : GuardIndex J G → {p : ℕ // p.Prime}) (pinj : Function.Injective prime)
    (guard : (i : GuardIndex J G) → RatFunc ℚ →+* ℚ_[(prime i).val])
    (hguard : ∀ i, v (guardSite i) =
      @EvaluationDVR.valuation (prime i).val ⟨(prime i).property⟩ _ _ (guard i))

/-- The full guard profile is finitely supported even before subtracting its
target. Thus the correction is a finite product in the scalar field. -/
def guardCorrection (t : Profile J G H) : GuardIndex J G →₀ ℤ :=
  t.guardPart - (signed (weightedProduct (fun i => horizontalUnit (horizontal i)) t.horizontalPart)).guardPart

def splitCoarse (negate : Bool) (t : Profile J G H) : (RatFunc ℚ)ˣ :=
  coarseFactor negate (fun i => horizontalUnit (horizontal i)) prime
    t.horizontalPart (guardCorrection signed horizontal t)

include hval hinj hhor pinj hguard in
/-- The explicit signed product realizes both prescribed parts. At a
horizontal valuation every rational prime is a unit, and at a guard exactly
its own rational prime contributes scalar order one. -/
theorem splitCoarse_parts (negate : Bool) (t : Profile J G H) :
    let b := splitCoarse signed horizontal prime negate t
    (signed b).horizontalPart = t.horizontalPart ∧ (signed b).guardPart = t.guardPart := by
  classical
  constructor
  · ext i
    rw [Profile.horizontalPart_apply, hval, splitCoarse, coarseFactor_order]
    have hp (j : GuardIndex J G) : order (v (horizontalSite i)) ((prime j).val : RatFunc ℚ) = 0 := by
      rw [hhor, show ((prime j).val : RatFunc ℚ) = RatFunc.C ((prime j).val : ℚ) from (map_natCast _ _).symm,
        order, HorizontalOrders.valuation_constant _ _ (Nat.cast_ne_zero.mpr (prime j).property.ne_zero)]
      simp
    have hh (j : HorizontalIndex H) :
        order (v (horizontalSite i)) (horizontalUnit (horizontal j) : RatFunc ℚ) =
          if j = i then 1 else 0 := by
      rw [hhor]
      change order _ (PrincipalProfiles.factor (horizontal j)) = _
      by_cases he : j = i
      · subst j
        simp [order]
      · simp [order, HorizontalOrders.valuation_factor_of_ne _ _ (fun he' => he (hinj he')), he]
    simp [hp, hh]
    exact Eq.symm
  · ext i
    rw [Profile.guardPart_apply, hval, splitCoarse, coarseFactor_order]
    have hp (j : GuardIndex J G) :
        order (v (guardSite i)) ((prime j).val : RatFunc ℚ) = if j = i then 1 else 0 := by
      let p := (prime i).val
      let : Fact p.Prime := ⟨(prime i).property⟩
      rw [hguard]
      change order (EvaluationDVR.valuation p (guard i)) ((prime j).val : RatFunc ℚ) = _
      by_cases he : j = i
      · subst j
        simp [order, ← show p = (prime i).val from rfl]
      · let q := (prime j).val
        let : Fact q.Prime := ⟨(prime j).property⟩
        have hne : q ≠ p := fun heq => he (pinj (Subtype.ext heq))
        simp [order, PairedResidues.valuation_prime_eq_one_of_ne q p (guard i) hne, he, ← show q = (prime j).val from rfl]
    simp only [hp, weighted_single]
    rw [← weightedProduct_order, guardCorrection, Finsupp.sub_apply]
    simp only [Profile.guardPart_apply, hval]
    abel

include hval hinj hhor pinj hguard in
theorem splitCoarse_coordinates (negate : Bool) (t : Profile J G H) :
    let b := splitCoarse signed horizontal prime negate t
    (signed b).height = t.height ∧ (signed b).guards = t.guards ∧
      (signed b).horizontal = t.horizontal := by
  obtain ⟨hh,hg⟩ := splitCoarse_parts v signed hval horizontal hinj hhor prime pinj guard hguard negate t
  refine ⟨funext (fun k => DFunLike.congr_fun hh (.inl k)), ?_,
    Finsupp.ext (fun i => DFunLike.congr_fun hh (.inr i))⟩
  apply Guards.ext_of_components
  · exact funext (fun k => Finsupp.ext (fun n => DFunLike.congr_fun hg (.inl (k,n))))
  · exact funext (fun k => Finsupp.ext (fun n => DFunLike.congr_fun hg (.inr (.inl (k,n)))))
  · exact funext (fun k => Finsupp.ext (fun j => DFunLike.congr_fun hg (.inr (.inr (.inl ⟨k,j⟩)))))
  · exact Finsupp.ext (fun g => DFunLike.congr_fun hg (.inr (.inr (.inr g))))

include hval in
/-- At the reserved minus site the earlier coarse factor vanishes in order
when its selected horizontal factors and scalar corrections are units there. -/
theorem splitCoarse_minus_zero (negate : Bool) (t : Profile J G H) (M : ℕ)
    (hh : ∀ i ∈ t.horizontalPart.support,
      order (v (.minus true M)) (horizontalUnit (horizontal i) : RatFunc ℚ) = 0)
    (hp : ∀ i ∈ (guardCorrection signed horizontal t).support,
      order (v (.minus true M)) ((prime i).val : RatFunc ℚ) = 0) :
    (signed (splitCoarse signed horizontal prime negate t)).minus true M = 0 := by
  change (signed _).signedValues (.minus true M) = _
  rw [hval, splitCoarse, coarseFactor_order]
  unfold Finsupp.sum
  rw [Finset.sum_eq_zero (fun i hi => by simp only [hh i hi, mul_zero]),
    Finset.sum_eq_zero (fun i hi => by simp only [hp i hi, mul_zero]), add_zero]

end UnconditionalCounterexample.DyadicSplit
