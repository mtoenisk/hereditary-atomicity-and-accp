import UnconditionalCounterexample.Variations.TwoChainTargets
import UnconditionalCounterexample.Variations.UnivariateClient
import UnconditionalCounterexample.Variations.UnivariateRecovery
import UnconditionalCounterexample.AtomProfiles

/-!
# The two-colour domain from its actual prime-allocation sequence

The generator stages introduce the two even pivots and then the two
interleaved families of b and q generators. A primary is attached once, at the
first stage where its coordinate has nonzero weight.
-/

noncomputable section
namespace UnconditionalCounterexample.TwoChains

open GuardSupport Filter WithZero NormalizedWords
open Variations Univariate UnivariateConductor TwoChainSchedule
local instance : Algebra ℚ (RatFunc ℚ) := RatFunc.instAlgebraOfPolynomial ℚ ℚ

def family : UnivariateClient.Family where
  colour n := (decode n).1
  order := displacementOrder
  positive := displacementOrder_pos
  targets P _ B sites := TwoChains.targets P B sites

abbrev requirements := family.requirements
abbrev domain := Univariate.domain requirements
abbrev raw := (chain requirements).raw
abbrev generators := (chain requirements).generators
abbrev guard (p : PrimeIndex) := (permanentSite requirements p).guard

def guardVal (p : PrimeIndex) : Valuation (RatFunc ℚ) ℤᵐ⁰ :=
  EvaluationDVR.evaluationValuation p.val (guard p).val (permanentSite requirements p).guard_trans

/-- A primary is indexed by its colour and its coordinate in that tail. -/
abbrev pairedPrime (c : Bool) (i : ℕ) := family.prime (allocationStage c i)
abbrev primary (c : Bool) (i : ℕ) := (family.atStage (allocationStage c i)).primary

def primaryAtStage (k : ℕ) : Valuation (RatFunc ℚ) ℤᵐ⁰ :=
  EvaluationDVR.evaluationValuation (family.prime k).val
    (family.atStage k).primary.val.val (family.atStage k).primary.property.1

abbrev primaryVal (c : Bool) (i : ℕ) := primaryAtStage (allocationStage c i)

def vertical : (Bool × ℕ ⊕ PrimeIndex) → Valuation (RatFunc ℚ) ℤᵐ⁰ :=
  Sum.elim (fun z => primaryVal z.1 z.2) guardVal

@[simp] theorem allocated_label (c : Bool) (j : ℕ) :
    (decode (allocationStage c j)).1 = c ∧
      newIndex (decode (allocationStage c j)).2 = j := by
  obtain ⟨n, rfl | rfl⟩ : ∃ n, j = 2*n ∨ j = 2*n+1 := ⟨j/2, by omega⟩
  · simp [newIndex]
  · simp [newIndex]


@[simp] theorem allocate_newIndex (k : ℕ) :
    allocationStage (decode k).1 (newIndex (decode k).2) = k := by
  obtain ⟨c, g, rfl⟩ := stage_surjective k
  cases g <;> simp [newIndex]

theorem pairPrime_injective (c : Bool) : Function.Injective (pairedPrime c) := by
  intro i j h
  have he := congrArg (fun k => newIndex (decode k).2) (family.prime_injective h)
  simpa only [(allocated_label c i).2, (allocated_label c j).2] using he

private theorem all_points {x : RatFunc ℚ} :
    (∀ p (a : Point p), a ∈ (permanentSite requirements p).fibre.points →
      LocalEvaluation.evalAt a.value.val a.transcendental x ∈ PadicInt.subring p.val) ↔
      (∀ j, vertical j x ≤ 1) := by
  constructor
  · intro hall j
    rcases j with ⟨c, i⟩ | p
    · let k := allocationStage c i
      let a : Point (family.prime k) :=
        ⟨(family.atStage k).primary.val, (family.atStage k).primary.property.1⟩
      have hm : a ∈ (permanentSite requirements (family.prime k)).fibre.points := by
        rw [family.permanent_eq]
        exact Set.mem_insert _ _
      exact (EvaluationDVR.mem_valuationSubring _ _ _).mpr (hall _ a hm)
    · let s := permanentSite requirements p
      let a : Point p := ⟨s.guard, s.guard_trans⟩
      have hm : a ∈ s.fibre.points := by
        cases h : s.primary <;> simp [Site.fibre, h, Fibre.points, a]
      exact (EvaluationDVR.mem_valuationSubring _ _ _).mpr (hall _ a hm)
  · intro hall p a ha
    obtain ⟨b, hb, he⟩ := (permanentSite requirements p).branch_of_point ha
    cases b with
    | true =>
      have hh := (EvaluationDVR.mem_valuationSubring _ _ x).mp (hall (.inr p))
      change (guard p).val = a.value.val at he
      have he' : (⟨guard p, (permanentSite requirements p).guard_trans⟩ : Point p) = a := by
        cases a
        congr 1
        exact Subtype.ext he
      subst a
      exact hh
    | false =>
      obtain ⟨k, rfl⟩ := (family.paired_iff p).mp (hb.resolve_left (by decide))
      rw [family.permanent_eq] at he
      change (family.atStage k).primary.val.val = a.value.val at he
      have ha' : (⟨(family.atStage k).primary.val, (family.atStage k).primary.property.1⟩ :
          Point (family.prime k)) = a := by
        cases a
        congr 1
        exact Subtype.ext he
      subst a
      have hval := hall (.inl ((decode k).1, newIndex (decode k).2))
      change primaryAtStage (allocationStage (decode k).1 (newIndex (decode k).2)) x ≤ 1 at hval
      rw [allocate_newIndex] at hval
      exact (EvaluationDVR.mem_valuationSubring _ _ x).mp hval

/-- The valuations indexed by the two primary tails and all ordinary guards
define exactly the domain attached to the adaptive sequence. -/
theorem domain_eq_intersection : domain =
    IntersectionDomain.intersection (poleAlgebra requirements).toSubring vertical := by
  ext x
  rw [Univariate.mem_domain_iff, IntersectionDomain.mem_intersection, all_points]
  rfl

theorem primary_seed (c d : Bool) (j : ℕ) :
    primaryVal d j (seed c) = exp (-(if c = d then primaryAtomProfile 0 j else 0)) := by
  let k := allocationStage d j
  let α := (family.atStage k).primary
  have colour : family.colour k = d := (allocated_label d j).1
  have disp : (family.order k : ℤ) = primaryAtomProfile 0 j := by
    change ((if newIndex (decode k).2 = 0 then 2 else 1 : ℕ) : ℤ) = _
    rw [(allocated_label d j).2]
    simp [primaryAtomProfile]
  have hn := primary_seed_norm (family.atStage k).odd α.val d (family.order k)
    α.property.1 (colour ▸ (family.atStage k).hr) (colour ▸ (family.atStage k).hv)
  change Padic.mulValuation (EvaluationDVR.evaluationHom _ α.val.val α.property.1 (seed c)) = _
  rw [eval_seed]
  by_cases hcd : c = d
  · subst c
    have hval := ReturnTargets.valuation_of_target_norm (family.order k) (0 : ℚ_[(family.prime k).val])
      (seedValue α.val.val d) (hn.1.trans (ReturnTargets.quotientTarget_norm _ _).symm)
    have hne := norm_pos_iff.mp (hn.1 ▸ zpow_pos
      (by exact_mod_cast (family.prime k).property.pos : (0 : ℝ) < (family.prime k).val) _)
    simp only [Padic.mulValuation_toFun, hne, ite_false, hval, eq_self, ite_true, disp]
  · have hc : c = !d := by cases c <;> cases d <;> simp_all
    simp only [ite_eq_right hcd, neg_zero, exp_zero]
    exact mulValuation_eq_one_of_norm_eq_one _ (hc ▸ hn.2)

theorem guard_seed (p : PrimeIndex) (c : Bool) : guardVal p (seed c) = 1 := by
  change Padic.mulValuation (EvaluationDVR.evaluationHom _ _ _ (seed c)) = 1
  rw [eval_seed]
  apply mulValuation_eq_one_of_norm_eq_one
  by_cases he : p.val = 2
  · have hp : p = ⟨2, Nat.prime_two⟩ := Subtype.ext he
    subst p
    exact dyadic_seed_norm (guard ⟨2, Nat.prime_two⟩) family.dyadic_guard_only.2 c
  · have h₀ : PadicInt.toZMod (guard p) ≠ 0 := by
      apply (padicInt_isUnit_iff_toZMod_ne_zero _).mp
      rw [guard, Univariate.permanent_guard_eq]
      exact (chain requirements).guardChain.value_unit p
    exact odd_guard_seed_norm (p := p.val) (by have := p.property.two_le; omega) (guard p) h₀
      ((family.guard_residues p).2 he) c

/-- Stabilization at each translated horizontal order on its actual prime tail. -/
theorem eventually_primary_order (c : Bool) (x : RatFunc ℚ) (hx : x ≠ 0) :
    ∀ᶠ i in atTop, DiscreteOrders.order (primaryVal c i) x =
      UnivariateCentres.orderAt (if c then 1 else 0) x := by
  let p (i : ℕ) := (pairedPrime c i).val
  let γ (i : ℕ) : ℚ_[p i] := (primary c i).val.val
  have hv : ∀ᶠ i in atTop, (γ i - ((if c then 1 else 0 : ℚ) : ℚ_[p i])).valuation = 1 := by
    filter_upwards [eventually_ge_atTop 1] with i hi
    have h := (family.atStage (allocationStage c i)).hv
    change (γ i - (if (decode (allocationStage c i)).1 then 1 else 0)).valuation =
      ((if newIndex (decode (allocationStage c i)).2 = 0 then 2 else 1 : ℕ) : ℤ) at h
    have hi0 : i ≠ 0 := by omega
    rw [(allocated_label c i).1, (allocated_label c i).2, show (if i=0 then 2 else 1 : ℕ) = 1 by simp [hi0]] at h
    cases c <;> simpa using h
  filter_upwards [UnivariateCentres.eventually_order_at (if c then 1 else 0) p
    (Subtype.val_injective.comp (pairPrime_injective c)) γ (fun i => (primary c i).property.1)
    hv x hx] with i hi
  change -log (Padic.mulValuation (EvaluationDVR.evaluationHom (p i) (γ i) (primary c i).property.1 x)) = _
  have hn : EvaluationDVR.evaluationHom (p i) (γ i) (primary c i).property.1 x ≠ 0 :=
    (map_ne_zero_iff _ (EvaluationDVR.evaluationHom _ _ _).injective).mpr hx
  simp only [Padic.mulValuation_toFun, hn, ite_false, log_exp, neg_neg]
  exact hi

end UnconditionalCounterexample.TwoChains
