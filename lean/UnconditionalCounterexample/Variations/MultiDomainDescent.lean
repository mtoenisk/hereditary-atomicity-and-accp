import UnconditionalCounterexample.Variations.MultiDomain
import UnconditionalCounterexample.ProfileCriterion
import UnconditionalCounterexample.LowOrderDivisors
import UnconditionalCounterexample.FiniteDivisorBounds

/-!
# Low-order divisors and hereditary descent at the reserved rational point

The ordinary valuation profile supplies the low-order bound and the late
moving divisors. A moving divisor whose point value is a local unit still
divides in the embedded pullback. Integer returns there are tested by the
ordinary return and the local congruence at the point.
-/

noncomputable section
namespace UnconditionalCounterexample.Variations.MultiDomain

open Filter FiniteDivisorBounds
open scoped Topology

variable {r : ℕ} {A : Data r} {ι : Type*}

/-- The ordinary coordinate system and the order-one sequence it realizes. -/
structure DescentData (A : Data r) (ι : Type*) where
  profile : ValuationProfiles (ordinary A) ι
  divides : ∀ x y : ordinary A, x ≠ 0 → y ≠ 0 →
    (∀ p, profile.value p x ≤ profile.value p y) → x ∣ y
  signs : ∀ x : ordinary A, IsUnit x → x = 1 ∨ x = -1
  a : ℕ → ordinary A
  nonzero : ∀ n, a n ≠ 0
  order_one : ∀ n, profile.value .limit (a n) = 1
  outside_zero : ∀ n i, profile.value (.outside i) (a n) = 0
  moving_primary : ∀ n j, (profile.value (.primary j) (a n) : ℤ) = primaryAtomProfile n j

namespace DescentData

variable (H : DescentData A ι)

theorem moving_irreducible (n : ℕ) : Irreducible (H.a n) :=
  H.profile.irreducible_of_primaryAtomProfile (H.nonzero n) n (H.order_one n)
    (H.outside_zero n) (H.moving_primary n)

theorem eventually_moving_dvd {x : ordinary A} (hx : x ≠ 0)
    (hord : 2 ≤ H.profile.value .limit x) : ∀ᶠ n in atTop, H.a n ∣ x :=
  eventually_atTop.mpr (H.profile.eventually_dvd_of_primaryAtomProfiles H.divides H.a
    H.nonzero H.order_one H.outside_zero H.moving_primary hx hord)

theorem finite_divisors {x : ordinary A} (hx : x ≠ 0) (ho : H.profile.value .limit x ≤ 1)
    (htr : H.profile.SignedDifferenceTriple) : {z : ordinary A | z ∣ x}.Finite :=
  finite_divisors_of_finite_classes H.signs
    (H.profile.finite_associates_divisors_of_limit_le_one htr H.divides hx ho)

theorem ordinary_hereditarilyAtomic
    (hret : ∀ m : ℕ, 0 < m → ∀ᶠ n in atTop, (m : ordinary A) ∣ H.a n - 1)
    (hcond : ∀ T : Subring (ordinary A), ¬ Factorization.IsBFDomain T →
      ∃ m : ℕ, 0 < m ∧ ∀ z : ordinary A, (m : ordinary A) * z ∈ T) :
    Factorization.IsHereditarilyAtomic (ordinary A) :=
  hereditarilyAtomic_of_profiles_and_integerConductors H.profile H.divides H.signs H.a
    H.nonzero H.order_one H.outside_zero H.moving_primary
    (fun m hm N ↦ ((hret m hm).and (eventually_ge_atTop N)).exists.imp
      fun _ h ↦ ⟨h.2, h.1⟩) hcond

end DescentData

variable (A) (c : Fin r → ℚ) (hc : MultivariateFibres.Retained (denominators A) c)
  (q : ℕ) [Fact q.Prime]

/-- The inclusion of the actual embedded point pullback in the ordinary domain. -/
def toOrdinary : pullback A c hc q →+* ordinary A :=
  Subring.inclusion (by rintro _ ⟨w, _, rfl⟩; exact w.property)

theorem toOrdinary_injective : Function.Injective (toOrdinary A c hc q) :=
  fun _ _ h ↦ Subtype.ext (congrArg (ordinary A).subtype h)

theorem point_toOrdinary_mem (x : pullback A c hc q) :
    point A c hc (toOrdinary A c hc q x) ∈ PointPullback.localRationals q := by
  obtain ⟨w, hw, heq⟩ := x.property
  exact (show w = toOrdinary A c hc q x from Subtype.ext heq) ▸ hw

def liftPoint (x : ordinary A) (hx : point A c hc x ∈ PointPullback.localRationals q) :
    pullback A c hc q := ⟨x, ⟨x, hx, rfl⟩⟩

@[simp] theorem toOrdinary_liftPoint (x : ordinary A) (hx : point A c hc x ∈ PointPullback.localRationals q) :
    toOrdinary A c hc q (liftPoint A c hc q x hx) = x := rfl

/-- The point value of the top may vanish. Only the divisor is required to
have invertible point value. -/
theorem dvd_pullback_of_point_unit {a x : pullback A c hc q}
    (hu : ∃ u : (PointPullback.localRationals q)ˣ,
      ((u : PointPullback.localRationals q) : ℚ) = point A c hc (toOrdinary A c hc q a))
    (hd : toOrdinary A c hc q a ∣ toOrdinary A c hc q x) : a ∣ x := by
  obtain ⟨b, hb⟩ := hd
  obtain ⟨u, hu⟩ := hu
  have hp := congrArg (point A c hc) hb
  rw [map_mul, ← hu] at hp
  let W := PointPullback.localRationals q
  have he : ((((u⁻¹ : Wˣ) : W) : ℚ) * point A c hc (toOrdinary A c hc q x)) =
      point A c hc b := by
    rw [hp, ← mul_assoc, ← Subring.coe_mul, u.inv_mul, Subring.coe_one, one_mul]
  refine ⟨liftPoint A c hc q b (he ▸ W.mul_mem ((u⁻¹ : Wˣ) : W).property
    (point_toOrdinary_mem A c hc q x)), ?_⟩
  exact (toOrdinary_injective A c hc q) hb

/-- Simultaneous ordinary and local divisibility by a positive integer. -/
theorem natCast_dvd_pullback {m : ℕ} (hm : 0 < m) {x : pullback A c hc q}
    (hd : (m : ordinary A) ∣ toOrdinary A c hc q x)
    (hp : point A c hc (toOrdinary A c hc q x) / m ∈ PointPullback.localRationals q) :
    (m : pullback A c hc q) ∣ x := by
  obtain ⟨b, hb⟩ := hd
  have he := congrArg (point A c hc) hb
  rw [map_mul, map_natCast] at he
  rw [he, mul_div_cancel_left₀ _ (Nat.cast_ne_zero.mpr hm.ne' : (m : ℚ) ≠ 0)] at hp
  refine ⟨liftPoint A c hc q b hp, ?_⟩
  apply toOrdinary_injective A c hc q
  simpa only [map_mul, map_natCast, toOrdinary_liftPoint] using hb

namespace DescentData

variable (H : DescentData A ι)
  (hu : ∀ n, ∃ u : (PointPullback.localRationals q)ˣ,
    ((u : PointPullback.localRationals q) : ℚ) = point A c hc (H.a n))

def pullbackMoving (n : ℕ) : pullback A c hc q :=
  liftPoint A c hc q (H.a n) (by obtain ⟨u, h⟩ := hu n; exact h ▸ (u : PointPullback.localRationals q).property)

include H in
theorem pullback_signs (x : pullback A c hc q) (hx : IsUnit x) : x = 1 ∨ x = -1 := by
  rcases H.signs _ (hx.map (toOrdinary A c hc q)) with h | h
  · exact Or.inl (toOrdinary_injective A c hc q (h.trans (map_one _).symm))
  · exact Or.inr (toOrdinary_injective A c hc q (by simpa using h))

include H in
theorem pullback_reflects_units {x : pullback A c hc q} (hx : IsUnit (toOrdinary A c hc q x)) :
    IsUnit x := by
  rcases H.signs _ hx with h | h
  · exact (toOrdinary_injective A c hc q (h.trans (map_one _).symm)) ▸ isUnit_one
  · have he : x = -1 := toOrdinary_injective A c hc q (by simpa using h)
    simp [he]

theorem finite_divisors_pullback (T : Subring (pullback A c hc q)) (x : T) (hx : x ≠ 0)
    (ho : H.profile.value .limit (toOrdinary A c hc q x) ≤ 1)
    (htr : H.profile.SignedDifferenceTriple) : {z : T | z ∣ x}.Finite := by
  let f := (toOrdinary A c hc q).comp T.subtype
  have hi : Function.Injective f := (toOrdinary_injective A c hc q).comp Subtype.val_injective
  apply ((H.finite_divisors (show f x ≠ 0 from fun h ↦ hx (hi (h.trans f.map_zero.symm)))
    ho htr).preimage hi.injOn).subset
  exact fun _ h ↦ map_dvd f h

theorem eventually_pullbackMoving_dvd {x : pullback A c hc q} (hx : x ≠ 0)
    (ho : 2 ≤ H.profile.value .limit (toOrdinary A c hc q x)) :
    ∀ᶠ n in atTop, H.pullbackMoving A c hc q hu n ∣ x := by
  apply (H.eventually_moving_dvd (fun h ↦ hx ((toOrdinary_injective A c hc q)
    (h.trans (map_zero _).symm))) ho).mono
  exact fun n h ↦ dvd_pullback_of_point_unit A c hc q (hu n) h

theorem eventually_pullbackMoving_return (m : ℕ) (hm : 0 < m)
    (hd : ∀ᶠ n in atTop, (m : ordinary A) ∣ H.a n - 1)
    (hp : ∀ᶠ n in atTop, (point A c hc (H.a n) - 1) / m ∈ PointPullback.localRationals q) :
    ∀ᶠ n in atTop, (m : pullback A c hc q) ∣ H.pullbackMoving A c hc q hu n - 1 := by
  filter_upwards [hd, hp] with n hn hq
  apply natCast_dvd_pullback A c hc q hm
  · simpa only [map_sub, map_one, pullbackMoving, toOrdinary_liftPoint] using hn
  · simpa only [map_sub, map_one, pullbackMoving, toOrdinary_liftPoint] using hq

include hu in
theorem pullback_hereditarilyAtomic
    (hord : ∀ m : ℕ, 0 < m → ∀ᶠ n in atTop, (m : ordinary A) ∣ H.a n - 1)
    (hpoint : ∀ m : ℕ, 0 < m →
      ∀ᶠ n in atTop, (point A c hc (H.a n) - 1) / m ∈ PointPullback.localRationals q)
    (hcond : ∀ T : Subring (pullback A c hc q), ¬ Factorization.IsBFDomain T →
      ∃ m : ℕ, 0 < m ∧ ∀ z : pullback A c hc q, (m : pullback A c hc q) * z ∈ T) :
    Factorization.IsHereditarilyAtomic (pullback A c hc q) := by
  let f := toOrdinary A c hc q
  have hn {x : pullback A c hc q} (hx : x ≠ 0) : f x ≠ 0 :=
    fun h ↦ hx ((toOrdinary_injective A c hc q) (h.trans f.map_zero.symm))
  apply hereditarilyAtomic_of_integerConductors (H.pullback_signs A c hc q)
    (fun x ↦ H.profile.value .limit (f x)) (fun x y hx hy ↦ by
      rw [map_mul, H.profile.value_mul _ _ _ (hn hx) (hn hy)])
    (fun x hx ho ↦ Factorization.hasBoundedFactorizations_of_unitReflectingMap f.toMonoidHom
      (fun _ h ↦ H.pullback_reflects_units A c hc q h)
      (H.profile.hasBoundedFactorizations_of_limit_le_one (hn hx) ho))
    (H.pullbackMoving A c hc q hu) H.order_one (fun _ hx ho ↦
      eventually_atTop.mp (H.eventually_pullbackMoving_dvd A c hc q hu hx ho)) _ hcond
  intro m hm N
  exact ((H.eventually_pullbackMoving_return A c hc q hu m hm (hord m hm) (hpoint m hm)).and
    (eventually_ge_atTop N)).exists.imp fun _ h ↦ ⟨h.2, h.1⟩

end DescentData
end UnconditionalCounterexample.Variations.MultiDomain
