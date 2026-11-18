import UnconditionalCounterexample.FractionalIdealMinima
import UnconditionalCounterexample.PaperAtoms
import UnconditionalCounterexample.PaperSpectrum
import UnconditionalCounterexample.LocalInvertibility
import UnconditionalCounterexample.PicardProfiles
import Mathlib.RingTheory.ClassGroup.Basic

/-!
# The actual restricted profile map for invertible fractional ideals

The domain and every valuation are those of PaperConstruction. Finite generation
proves eventual primary stabilization and finite outside support for actual
invertible fractional ideals. The resulting map to PicardProfiles.Profile is
additive and injective; principal ideals have the literal element profile.
Surjectivity is a separate construction of singleton and tail ideal profiles.
-/

namespace UnconditionalCounterexample.PaperIdealProfiles

open WithZero CompleteProfiles PaperConstruction FractionalIdealProfiles
open scoped nonZeroDivisors

abbrev Label := ProfilePlace (Outside poles)
abbrev Fractional := FractionalIdeal domain⁰ (RatFunc ℚ)
noncomputable abbrev v : Label → Valuation (RatFunc ℚ) ℤᵐ⁰ := valuations poles places

local instance : IsFractionRing domain (RatFunc ℚ) := fractionRing

theorem integral (l : Label) (r : domain) : v l (algebraMap domain (RatFunc ℚ) r) ≤ 1 :=
  CompleteProfiles.integral poles places (fun _ hf => raw_constant hf) r l

theorem full (x : RatFunc ℚ) : x ∈ (1 : Fractional) ↔ ∀ l, v l x ≤ 1 := by
  constructor
  · intro hx
    obtain ⟨r, rfl⟩ := (FractionalIdeal.mem_one_iff domain⁰).mp hx
    exact fun l => integral l r
  · intro hx
    have hxd : x ∈ domain := by
      change x ∈ PairedDomain.domain poles places
      rw [CompleteProfiles.domain_eq_fullIntersection poles places (fun _ hf => raw_constant hf)]
      exact (IntersectionDomain.mem_intersection ⊤ (valuations poles places) x).mpr ⟨Subring.mem_top x, hx⟩
    exact (FractionalIdeal.mem_one_iff domain⁰).mpr ⟨⟨x, hxd⟩, rfl⟩

/-- Actual invertibility follows from the proved DVR stalks, not from a
Noetherian or Dedekind instance on this domain. -/
theorem isUnit_of_fg (I : Fractional) (hfg : (I : Submodule domain (RatFunc ℚ)).FG) (hI : I ≠ 0) :
    IsUnit I :=
  LocalInvertibility.fractional_isUnit_of_local_dvr isAlmostDedekindDomain I hfg hI

noncomputable def profileFunction : Additive Fractionalˣ →+ (Label → ℤ) :=
  profileHom v integral

theorem profileFunction_injective : Function.Injective profileFunction :=
  profileHom_injective v integral full

theorem principal_restricted (x : RatFunc ℚ) (hx : x ≠ 0) :
    PicardProfiles.Restricted (fun l => DiscreteOrders.order (v l) x) := by
  exact ⟨eventually_primary poles places x hx, finite_outside poles places guardSupport x hx⟩

/-- Actual invertible ideal profiles satisfy precisely the source's necessary
finite-support and eventual-primary restrictions, by finite generation. -/
theorem profileFunction_restricted (I : Additive Fractionalˣ) :
    PicardProfiles.Restricted (profileFunction I) := by
  classical
  obtain ⟨s, hs⟩ := FractionalIdeal.fg_unit I.toMul
  have hlim : HasValue I.toMul.val (v .limit) (profileFunction I .limit) :=
    value_spec (v .limit) (integral .limit) I.toMul
  constructor
  · have hev (x : RatFunc ℚ) (_hx : x ∈ s) :
        ∀ᶠ j : ℕ in Filter.atTop, v (.primary j) x = v .limit x := by
      by_cases hx0 : x = 0
      · exact Filter.Eventually.of_forall (fun j => by simp only [hx0, map_zero])
      · obtain ⟨N, hN⟩ := eventually_primary poles places x hx0
        filter_upwards [Filter.eventually_ge_atTop N] with j hj
        rw [DiscreteOrders.value_eq_exp_neg_order _ hx0,
          DiscreteOrders.value_eq_exp_neg_order _ hx0, hN j hj]
    have hall : ∀ᶠ j : ℕ in Filter.atTop, ∀ x ∈ s, v (.primary j) x = v .limit x :=
      (Filter.eventually_all_finset s).mpr hev
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hall
    refine ⟨N, fun j hj => ?_⟩
    exact (value_spec (v (.primary j)) (integral (.primary j)) I.toMul).unique
      (hlim.of_generators_eq (integral .limit) (integral (.primary j)) s hs
        (fun x hx => (hN j hj x hx).symm))
  · let bad (x : RatFunc ℚ) : Set (Outside poles) :=
      {o | x ≠ 0 ∧ DiscreteOrders.order (v (.outside o)) x ≠ 0}
    have hbad (x : RatFunc ℚ) : (bad x).Finite := by
      by_cases hx : x = 0
      · simp only [bad, hx, ne_eq, not_true_eq_false, false_and, Set.ofPred_false, Set.finite_empty]
      · exact (finite_outside poles places guardSupport x hx).subset (fun _ h => h.2)
    have hu : (⋃ x ∈ (s : Set (RatFunc ℚ)), bad x).Finite :=
      s.finite_toSet.biUnion (fun x _ => hbad x)
    apply hu.subset
    intro o ho
    by_contra hnot
    have hz (x : RatFunc ℚ) (hx : x ∈ s) (hx0 : x ≠ 0) : v (.outside o) x = 1 := by
      apply (DiscreteOrders.order_eq_zero_iff _ hx0).mp
      by_contra hv
      exact hnot (Set.mem_iUnion.mpr ⟨x, Set.mem_iUnion.mpr ⟨hx, hx0, hv⟩⟩)
    have hzero : HasValue I.toMul.val (v (.outside o)) 0 := by
      apply hasValue_of_span (v (.outside o)) (integral (.outside o)) I.toMul.val (s : Set _) hs 0
      · intro x hx
        by_cases hx0 : x = 0
        · simp only [hx0, map_zero, zero_le]
        · rw [hz x hx hx0]
          simp
      · obtain ⟨x, hx, hv⟩ := hlim.generator_attains (integral .limit) s hs
        have hx0 : x ≠ 0 := by
          intro hx0
          rw [hx0, map_zero] at hv
          exact exp_ne_zero hv.symm
        exact ⟨x, hx, by simpa only [neg_zero, exp_zero] using hz x hx hx0⟩
    exact ho ((value_spec (v (.outside o)) (integral (.outside o)) I.toMul).unique hzero)

/-- The actual invertible-ideal profile map with values in the exact restricted
tuple group used in the paper's Picard calculation. -/
noncomputable def profileMap : Additive Fractionalˣ →+ PicardProfiles.Profile (Outside poles) where
  toFun I := PicardProfiles.ofCoordinates (profileFunction I) (profileFunction_restricted I)
  map_zero' := by
    apply PicardProfiles.coordinate_injective
    rw [PicardProfiles.coordinate_ofCoordinates, map_zero, map_zero]
  map_add' I J := by
    apply PicardProfiles.coordinate_injective
    rw [PicardProfiles.coordinate_ofCoordinates, map_add, map_add,
      PicardProfiles.coordinate_ofCoordinates, PicardProfiles.coordinate_ofCoordinates]

@[simp] theorem coordinate_profileMap (I : Additive Fractionalˣ) :
    PicardProfiles.coordinate (profileMap I) = profileFunction I :=
  PicardProfiles.coordinate_ofCoordinates (profileFunction I) (profileFunction_restricted I)

theorem profileMap_injective : Function.Injective profileMap := by
  intro I J h
  apply profileFunction_injective
  simpa only [coordinate_profileMap] using congrArg PicardProfiles.coordinate h

/-- Nonzero principal fractional ideals have the literal element valuation profile. -/
theorem principal_profile (x : (RatFunc ℚ)ˣ) (l : Label) :
    PicardProfiles.coordinate (profileMap (Additive.ofMul (toPrincipalIdeal domain (RatFunc ℚ) x))) l =
      DiscreteOrders.order (v l) (x : RatFunc ℚ) := by
  rw [coordinate_profileMap]
  apply (value_spec (v l) (integral l) _).unique
  change HasValue ((toPrincipalIdeal domain (RatFunc ℚ) x : (FractionalIdeal domain⁰ (RatFunc ℚ))ˣ) : Fractional) (v l) _
  rw [coe_toPrincipalIdeal]
  exact hasValue_spanSingleton (v l) (integral l) (x : RatFunc ℚ) (Units.ne_zero x)

end UnconditionalCounterexample.PaperIdealProfiles
