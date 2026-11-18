import UnconditionalCounterexample.SparseProfileData
import UnconditionalCounterexample.SparseSpectrum
import UnconditionalCounterexample.FractionalIdealMinima
import UnconditionalCounterexample.LocalInvertibility
import Mathlib.RingTheory.ClassGroup.Basic

/-!
# Actual ideal profiles for a realized sparse construction

Finite generators give eventual primary stabilization and finite outside
support. Full-intersection membership proves injectivity of the actual
invertible fractional ideal profile map. All inputs belong to the same
SparseProfileData.Data; the maximal DVR theorem supplies actual invertibility.
-/

namespace UnconditionalCounterexample.SparseIdealProfiles

open WithZero SparseProfiles SparseProfileData FractionalIdealProfiles
open scoped nonZeroDivisors

variable (A : Data)

abbrev Fractional := FractionalIdeal A.domain⁰ (RatFunc ℚ)
noncomputable abbrev v : A.Label → Valuation (RatFunc ℚ) ℤᵐ⁰ := A.valuations

local instance : IsFractionRing A.domain (RatFunc ℚ) := A.fractionRing

theorem integral (l : A.Label) (r : A.domain) : v A l (algebraMap A.domain (RatFunc ℚ) r) ≤ 1 :=
  SparseProfiles.integral A.poles A.places A.constant_nonzero r l

theorem full (x : RatFunc ℚ) : x ∈ (1 : Fractional A) ↔ ∀ l, v A l x ≤ 1 := by
  constructor
  · intro hx
    obtain ⟨r, rfl⟩ := (FractionalIdeal.mem_one_iff A.domain⁰).mp hx
    exact fun l => integral A l r
  · intro hx
    have hxd : x ∈ A.domain := by
      change x ∈ SparsePrimaryDomain.domain A.poles A.places
      rw [SparseProfiles.domain_eq_fullIntersection A.poles A.places A.constant_nonzero]
      exact (IntersectionDomain.mem_intersection ⊤ (valuations A.poles A.places) x).mpr ⟨Subring.mem_top x, hx⟩
    exact (FractionalIdeal.mem_one_iff A.domain⁰).mpr ⟨⟨x, hxd⟩, rfl⟩

/-- Actual invertibility follows from the proved DVR stalks, not from a
Noetherian or Dedekind instance on this A.domain. -/
theorem isUnit_of_fg (I : Fractional A) (hfg : (I : Submodule A.domain (RatFunc ℚ)).FG) (hI : I ≠ 0) :
    IsUnit I :=
  LocalInvertibility.fractional_isUnit_of_local_dvr
    (SparseSpectrum.every_maximal_stalk_isDVR A.raw A.exponent A.places
      A.columns.b A.columns.q A.columns.guard A.constant_ne_zero A.guardSupport) I hfg hI

noncomputable def profileFunction : Additive (Fractional A)ˣ →+ (A.Label → ℤ) :=
  profileHom (v A) (integral A)

theorem profileFunction_injective : Function.Injective (profileFunction A) :=
  profileHom_injective (v A) (integral A) (full A)

theorem principal_restricted (x : RatFunc ℚ) (hx : x ≠ 0) :
    PicardProfiles.Restricted (fun l => DiscreteOrders.order (v A l) x) := by
  exact ⟨eventually_primary A.poles A.places x hx, finite_outside A.poles A.places A.guardSupport x hx⟩

/-- Actual invertible ideal profiles satisfy precisely the source's necessary
finite-support and eventual-primary restrictions, by finite generation. -/
theorem profileFunction_restricted (I : Additive (Fractional A)ˣ) :
    PicardProfiles.Restricted (profileFunction A I) := by
  classical
  obtain ⟨s, hs⟩ := FractionalIdeal.fg_unit I.toMul
  have hlim : HasValue I.toMul.val (v A .limit) (profileFunction A I .limit) :=
    value_spec (v A .limit) (integral A .limit) I.toMul
  constructor
  · have hev (x : RatFunc ℚ) (_hx : x ∈ s) :
        ∀ᶠ j : ℕ in Filter.atTop, v A (.primary j) x = v A .limit x := by
      by_cases hx0 : x = 0
      · exact Filter.Eventually.of_forall (fun j => by simp only [hx0, map_zero])
      · obtain ⟨N, hN⟩ := eventually_primary A.poles A.places x hx0
        filter_upwards [Filter.eventually_ge_atTop N] with j hj
        rw [DiscreteOrders.value_eq_exp_neg_order _ hx0,
          DiscreteOrders.value_eq_exp_neg_order _ hx0, hN j hj]
    have hall : ∀ᶠ j : ℕ in Filter.atTop, ∀ x ∈ s, v A (.primary j) x = v A .limit x :=
      (Filter.eventually_all_finset s).mpr hev
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hall
    refine ⟨N, fun j hj => ?_⟩
    exact (value_spec (v A (.primary j)) (integral A (.primary j)) I.toMul).unique
      (hlim.of_generators_eq (integral A .limit) (integral A (.primary j)) s hs
        (fun x hx => (hN j hj x hx).symm))
  · let bad (x : RatFunc ℚ) : Set (A.Outside) :=
      {o | x ≠ 0 ∧ DiscreteOrders.order (v A (.outside o)) x ≠ 0}
    have hbad (x : RatFunc ℚ) : (bad x).Finite := by
      by_cases hx : x = 0
      · simp only [bad, hx, ne_eq, not_true_eq_false, false_and, Set.ofPred_false, Set.finite_empty]
      · exact (finite_outside A.poles A.places A.guardSupport x hx).subset (fun _ h => h.2)
    have hu : (⋃ x ∈ (s : Set (RatFunc ℚ)), bad x).Finite :=
      s.finite_toSet.biUnion (fun x _ => hbad x)
    apply hu.subset
    intro o ho
    by_contra hnot
    have hz (x : RatFunc ℚ) (hx : x ∈ s) (hx0 : x ≠ 0) : v A (.outside o) x = 1 := by
      apply (DiscreteOrders.order_eq_zero_iff _ hx0).mp
      by_contra hv
      exact hnot (Set.mem_iUnion.mpr ⟨x, Set.mem_iUnion.mpr ⟨hx, hx0, hv⟩⟩)
    have hzero : HasValue I.toMul.val (v A (.outside o)) 0 := by
      apply hasValue_of_span (v A (.outside o)) (integral A (.outside o)) I.toMul.val (s : Set _) hs 0
      · intro x hx
        by_cases hx0 : x = 0
        · simp only [hx0, map_zero, zero_le]
        · rw [hz x hx hx0]
          simp
      · obtain ⟨x, hx, hv⟩ := hlim.generator_attains (integral A .limit) s hs
        have hx0 : x ≠ 0 := by
          intro hx0
          rw [hx0, map_zero] at hv
          exact exp_ne_zero hv.symm
        exact ⟨x, hx, by simpa only [neg_zero, exp_zero] using hz x hx hx0⟩
    exact ho ((value_spec (v A (.outside o)) (integral A (.outside o)) I.toMul).unique hzero)

/-- The actual invertible-ideal profile map with values in the exact restricted
tuple group used in the paper's Picard calculation. -/
noncomputable def profileMap : Additive (Fractional A)ˣ →+ PicardProfiles.Profile (A.Outside) where
  toFun I := PicardProfiles.ofCoordinates (profileFunction A I) (profileFunction_restricted A I)
  map_zero' := by
    apply PicardProfiles.coordinate_injective
    rw [PicardProfiles.coordinate_ofCoordinates, map_zero, map_zero]
  map_add' I J := by
    apply PicardProfiles.coordinate_injective
    rw [PicardProfiles.coordinate_ofCoordinates, map_add, map_add,
      PicardProfiles.coordinate_ofCoordinates, PicardProfiles.coordinate_ofCoordinates]

@[simp] theorem coordinate_profileMap (I : Additive (Fractional A)ˣ) :
    PicardProfiles.coordinate (profileMap A I) = profileFunction A I :=
  PicardProfiles.coordinate_ofCoordinates (profileFunction A I) (profileFunction_restricted A I)

theorem profileMap_injective : Function.Injective (profileMap A) := by
  intro I J h
  apply profileFunction_injective A
  simpa only [coordinate_profileMap A] using congrArg PicardProfiles.coordinate h

/-- Nonzero principal fractional ideals have the literal element valuation profile. -/
theorem principal_profile (x : (RatFunc ℚ)ˣ) (l : A.Label) :
    PicardProfiles.coordinate (profileMap A (Additive.ofMul (toPrincipalIdeal A.domain (RatFunc ℚ) x))) l =
      DiscreteOrders.order (v A l) (x : RatFunc ℚ) := by
  rw [coordinate_profileMap A]
  apply (value_spec (v A l) (integral A l) _).unique
  change HasValue ((toPrincipalIdeal A.domain (RatFunc ℚ) x : (FractionalIdeal A.domain⁰ (RatFunc ℚ))ˣ) : Fractional A) (v A l) _
  rw [coe_toPrincipalIdeal]
  exact hasValue_spanSingleton (v A l) (integral A l) (x : RatFunc ℚ) (Units.ne_zero x)

end UnconditionalCounterexample.SparseIdealProfiles
