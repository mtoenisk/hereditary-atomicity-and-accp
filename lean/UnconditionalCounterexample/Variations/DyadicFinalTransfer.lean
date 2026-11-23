import UnconditionalCounterexample.Variations.DyadicConcreteIndex
import UnconditionalCounterexample.Variations.DyadicConclusion

/-! # Hereditary atomicity from the split property on the calibrated domain -/

noncomputable section
namespace UnconditionalCounterexample.Variations.DyadicLedger.Calibrated
open Univariate DiscreteOrders

variable (a : Policy)

/-- The form of the split property read by the final theorem, expressed
using actual rational-function valuations and divisibility inside the domain. -/
def HasSplits (A : Subring (RatFunc ℚ)) : Prop :=
  ∀ (x : A) (m : ℕ), (x : RatFunc ℚ) ≠ 0 → 0 < m →
    0 < order (valuation a (.centre false)) x.val → 0 < order (valuation a (.centre true)) x.val →
    ∃ (U V : A) (d e : ℕ), x = U*V ∧ order (valuation a (.centre true)) U.val = 0 ∧
      order (valuation a (.centre false)) V.val = 0 ∧
      m = d*e ∧ d.Coprime e ∧ (d : A) ∣ U-1 ∧ (e : A) ∣ V-1

theorem hereditary_of_splits (splits : HasSplits a (domain (driver a).requirements)) :
    Factorization.IsHereditarilyAtomic (domain (driver a).requirements) := by
  rw [domain_eq_intersection] at splits ⊢
  let D := realization a
  have height_at (x : fullIntersection (valuation a)) (c : Bool) :
      (D.regular x).height c = (order (valuation a (.centre c)) x.val).toNat :=
    realization_values a x (.centre c)
  apply (D.dyadic_conclusion (sign_units a) (fun x _ => finite_extra a x)
    (intersection_index a) ?_).1
  intro x m hx hm hx₀ hx₁
  rw [height_at] at hx₀ hx₁
  obtain ⟨u,v,d,e,he,hu,hv,hs,hc,hd,he'⟩ := splits x m
    (fun h => hx (Subtype.ext h)) hm (Int.pos_iff_toNat_pos.mpr hx₀) (Int.pos_iff_toNat_pos.mpr hx₁)
  exact ⟨u,v,d,e,he,by rw [height_at,hu]; rfl,by rw [height_at,hv]; rfl,hs,hc,hd,he'⟩

theorem conclusion_of_splits (splits : HasSplits a (domain (driver a).requirements)) :
    Factorization.IsHereditarilyAtomic (domain (driver a).requirements) ∧
    (∃ x y : domain (driver a).requirements, x ≠ 0 ∧ y ≠ 0 ∧
      ∀ d, d ∣ x → d ∣ y → ∃ u, ¬ IsUnit u ∧ d*u ∣ x ∧ d*u ∣ y) ∧
      ¬ Factorization.IsStronglyAtomicDomain (domain (driver a).requirements) ∧
      ¬ Factorization.IsWeakACCP (domain (driver a).requirements) :=
  ⟨hereditary_of_splits a splits, domain_pair_obstruction a⟩

end UnconditionalCounterexample.Variations.DyadicLedger.Calibrated
