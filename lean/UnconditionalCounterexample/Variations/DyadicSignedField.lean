import UnconditionalCounterexample.Variations.DyadicFiniteProfiles

/-!
# The signed valuation profile of every nonzero rational function

The actual centre heights give the eventual primary orders. Only finitely
many deviations occur on each regular sequence, and all auxiliary, guard and
retained horizontal supports are finite. This supplies a profile on the
entire rational function field.
-/

noncomputable section
namespace UnconditionalCounterexample.Variations.DyadicLedger.Calibrated
open Polynomial GuardSupport Univariate FreezingCalendar DiscreteOrders DyadicDeviations WithZero
open FieldGeneration

variable (a : Policy)

private theorem guard_support (x : (RatFunc ℚ)ˣ) :
    (Function.support (fun p : PrimeIndex => order (UnivariateExtraction.guardVal (driver a).requirements p) x.val)).Finite := by
  apply (UnivariateExtraction.guard_support (driver a).requirements x.val x.ne_zero).subset
  intro p hp h
  exact hp ((order_eq_zero_iff _ x.ne_zero).mpr h)

theorem scalar_primary_order (q : ℚ) (hq : q ≠ 0) (p : PrimeIndex) (h : ((driver a).permanentRole p).isSome) :
    order (primaryVal a p h) (scalarUnit q hq).val =
      order (UnivariateExtraction.guardVal (driver a).requirements p) (scalarUnit q hq).val := by
  rw [primaryVal,evaluation_order]
  unfold UnivariateExtraction.guardVal
  rw [evaluation_order]
  have hc : RatFunc.C q = (q : RatFunc ℚ) := map_ratCast RatFunc.C q
  simp only [scalarUnit, Units.val_mk0,hc,map_ratCast]

theorem scalar_regular (q : ℚ) (hq : q ≠ 0) (c k : Bool) :
    (Function.support (regDev a c k (scalarUnit q hq))).Finite := by
  let p (i : ℕ) := regularPrime a (c,k,i)
  apply ((guard_support a (scalarUnit q hq)).preimage
    (show Function.Injective p from fun _ _ h => congrArg (fun l : RegularLabel => l.2.2) (regularPrime_injective a h)).injOn).subset
  intro i hi hz
  apply hi
  change order (primaryVal a (p i) _) (scalarUnit q hq).val - _ = 0
  rw [scalar_primary_order]
  change order (UnivariateExtraction.guardVal (driver a).requirements (p i)) (scalarUnit q hq).val = 0 at hz
  rw [hz]
  change 0 - (-log (HorizontalOrders.valuation (centre c) (RatFunc.C q))) = 0
  rw [HorizontalOrders.valuation_constant _ q hq,log_one]
  rfl

theorem scalar_auxiliary (q : ℚ) (hq : q ≠ 0) (k : Bool) :
    (Function.support (auxOrder a k (scalarUnit q hq))).Finite := by
  apply ((guard_support a (scalarUnit q hq)).preimage (aux_prime_injective a k).injOn).subset
  intro j hj hz
  apply hj
  change order (primaryVal a j.prime _) (scalarUnit q hq).val = 0
  rw [scalar_primary_order]
  exact hz

private theorem finite_all {I : Type*} (v : (RatFunc ℚ)ˣ → I → ℤ) (h1 : ∀ i, v 1 i = 0)
    (hm : ∀ x y i, v (x*y) i = v x i + v y i) (hi : ∀ x i, v x⁻¹ i = -v x i)
    (hs : ∀ q hq, (Function.support (v (scalarUnit q hq))).Finite)
    (hf : ∀ f : Horizontal, f.val ∉ Set.range (chain (driver a).requirements).raw →
      (Function.support (v (horizontalUnit f))).Finite)
    (hg : ∀ n, (Function.support (v (generatorUnit (driver a) n))).Finite)
    (x : (RatFunc ℚ)ˣ) : (Function.support (v x)).Finite := by
  let S : Subgroup (RatFunc ℚ)ˣ :=
    { carrier := {x | (Function.support (v x)).Finite}
      one_mem' := by simp [Function.support,h1]
      mul_mem' := by
        intro x y hx hy
        apply (Set.Finite.union hx hy).subset
        intro j hj
        by_contra h
        rw [Set.mem_union,not_or] at h
        exact hj (by rw [hm,not_ne_iff.mp h.1,not_ne_iff.mp h.2,add_zero])
      inv_mem' := by
        intro x hx
        apply Set.Finite.subset hx
        intro i h hz
        exact h (by rw [hi,hz,neg_zero]) }
  have hall := subgroup_eq_top (driver a) S hs hf hg
  change x ∈ S
  rw [hall]
  trivial

theorem finite_regular (c k : Bool) (x : (RatFunc ℚ)ˣ) : (Function.support (regDev a c k x)).Finite := by
  apply finite_all a (regDev a c k) _ _ _ (fun q hq => scalar_regular a q hq c k) _
    (fun n => generator_regular a n c k) x
  · intro i
    simp [regDev]
  · intro u v i
    simp only [regDev,Units.val_mul,order_mul _ u.ne_zero v.ne_zero]
    omega
  · intro u i
    simp only [regDev,Units.val_inv_eq_inv_val,order_inv]
    omega
  · intro f hraw
    rcases dispatcher_every_horizontal (planner a) f with h | ⟨n,h,_⟩
    · exact (hraw h).elim
    · exact frozen_regular a h c k

theorem finite_aux (k : Bool) (x : (RatFunc ℚ)ˣ) : (Function.support (auxOrder a k x)).Finite := by
  apply finite_all a (auxOrder a k) _ _ _ (fun q hq => scalar_auxiliary a q hq k) _
    (fun n => generator_aux a n k) x
  · intro i
    simp [auxOrder]
  · intro u v i
    exact order_mul _ u.ne_zero v.ne_zero
  · intro u i
    simp [auxOrder,Units.val_inv_eq_inv_val]
  · intro f hraw
    rcases dispatcher_every_horizontal (planner a) f with h | ⟨n,h,_⟩
    · exact (hraw h).elim
    · exact frozen_aux a h k

private def guardFin {I : Type*} (x : (RatFunc ℚ)ˣ) (p : I → PrimeIndex) (inj : Function.Injective p) : I →₀ ℤ :=
  Finsupp.ofSupportFinite (fun i => order (UnivariateExtraction.guardVal (driver a).requirements (p i)) x.val)
    ((guard_support a x).preimage inj.injOn)

private theorem horizontal_finite (x : (RatFunc ℚ)ˣ) :
    (Function.support fun h : Horiz a => order (HorizontalOrders.valuation h.val) x.val).Finite := by
  apply (((HorizontalOrders.finite_valuation_support x.val x.ne_zero).preimage Subtype.val_injective.injOn)).subset
  intro i hi h
  exact hi ((order_eq_zero_iff _ x.ne_zero).mpr h)

private theorem regular_inj (c k : Bool) : Function.Injective (fun i : ℕ => regularPrime a (c,k,i)) :=
  fun _ _ h => congrArg (fun l : RegularLabel => l.2.2) (regularPrime_injective a h)

/-- The actual finitely supported profile of a nonzero rational function. -/
def signed (x : (RatFunc ℚ)ˣ) : Profile (Aux a) (Lone a) (Horiz a) where
  height c := order (HorizontalOrders.valuation (centre c)) x.val
  plusDeviation k := Finsupp.ofSupportFinite _ (finite_regular a false k x)
  minusDeviation k := Finsupp.ofSupportFinite _ (finite_regular a true k x)
  auxiliary k := Finsupp.ofSupportFinite _ (finite_aux a k x)
  guards :=
    { plus := fun k => guardFin a x _ (regular_inj a false k)
      minus := fun k => guardFin a x _ (regular_inj a true k)
      auxiliary := fun k => guardFin a x _ (aux_prime_injective a k)
      lone := guardFin a x _ Subtype.val_injective }
  horizontal := Finsupp.ofSupportFinite _ (horizontal_finite a x)

theorem signed_values (x : (RatFunc ℚ)ˣ) (i : Coordinates a) :
    (signed a x).signedValues i = order (valuation a i) x.val := by
  cases i with
  | centre => rfl
  | plus k n | minus k n =>
    simp only [signed,Profile.signedValues,Profile.plus,Profile.minus,Finsupp.ofSupportFinite_coe,
      regDev,valuation]
    omega
  | other j => cases j <;> rfl

end UnconditionalCounterexample.Variations.DyadicLedger.Calibrated
