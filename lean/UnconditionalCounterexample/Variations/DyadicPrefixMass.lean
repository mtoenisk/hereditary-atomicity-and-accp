import UnconditionalCounterexample.Variations.DyadicPrefixCoarse
import UnconditionalCounterexample.Variations.DyadicFieldGeneration

/-!
# The finite mass equations of the coarse factor

The finite table's coordinates are additive orders, including the copied
horizontal heights at its missing regular labels. Every rational scalar has
zero paired discrepancy. Thus calibration of the old horizontal factors
implies the mass equations for every finite coarse product used by the split.
-/

noncomputable section
namespace UnconditionalCounterexample.Variations.DyadicLedger.PrefixProfile
open Polynomial GuardSupport Univariate FreezingCalendar DiscreteOrders DyadicDeviations DyadicSplit Calibration

variable (A : Finset PrimeIndex) (role : PrimeIndex → Option FibreRole) (T : Table A) (K : Finset ℚ[X])

theorem signed_regular (hu : UniqueRegular A role) (x : (RatFunc ℚ)ˣ) {p : PrimeIndex} (hp : p ∈ A) {c k : Bool} {i : ℕ}
    (hr : role p = some (.regular c k i)) :
    regularValue (signed A role T K x) c k i = branchOrder A T x.val false p ∧
      regularGuard (signed A role T K x) c k i = branchOrder A T x.val true p :=
  actual_regular A role _ _ _ _ hu hp hr

theorem signed_missing (x : (RatFunc ℚ)ˣ) {c k : Bool} {i : ℕ} (h : ∀ p ∈ A, role p ≠ some (.regular c k i)) :
    regularValue (signed A role T K x) c k i = order (HorizontalOrders.valuation (centre c)) x.val ∧
      regularGuard (signed A role T K x) c k i = 0 := missing_regular A role _ _ _ _ h

private theorem branch_mul (x y : (RatFunc ℚ)ˣ) (p : PrimeIndex) (b : Bool) :
    branchOrder A T (x*y).val b p = branchOrder A T x.val b p + branchOrder A T y.val b p := by
  by_cases h : p ∈ A
  · by_cases hb : MixedStageSelection.Active (T p h).paired b
    · simp only [branchOrder,h,↓reduceDIte,branchValue,hb,Units.val_mul,map_mul]
      exact Padic.valuation_mul ((_root_.map_ne_zero _).mpr x.ne_zero) ((_root_.map_ne_zero _).mpr y.ne_zero)
    · simp [branchOrder,h,branchValue,hb]
  · simp [branchOrder,h]

theorem signed_values_mul (hu : UniqueRegular A role) (x y : (RatFunc ℚ)ˣ) (i) :
    (signed A role T K (x*y)).signedValues i =
      (signed A role T K x).signedValues i + (signed A role T K y).signedValues i := by
  let s := signed A role T K
  have reg (c k : Bool) (i : ℕ) : regularValue (s (x*y)) c k i = regularValue (s x) c k i + regularValue (s y) c k i ∧
      regularGuard (s (x*y)) c k i = regularGuard (s x) c k i + regularGuard (s y) c k i := by
    by_cases h : ∃ p ∈ A, role p = some (.regular c k i)
    · obtain ⟨p,hp,hr⟩ := h
      have atp := fun w => signed_regular A role T K hu w hp hr
      exact ⟨(atp _).1.trans ((branch_mul A T x y _ _).trans (congrArg₂ _ (atp _).1.symm (atp _).1.symm)),
        (atp _).2.trans ((branch_mul A T x y _ _).trans (congrArg₂ _ (atp _).2.symm (atp _).2.symm))⟩
    · have miss := fun p hp hr => h ⟨p,hp,hr⟩
      have outside := fun w => signed_missing A role T K w miss
      exact ⟨(outside _).1.trans ((order_mul _ x.ne_zero y.ne_zero).trans
        (congrArg₂ _ (outside _).1.symm (outside _).1.symm)),
        (outside _).2.trans (by rw [(outside _).2,(outside _).2,add_zero])⟩
  have hor (j : HorizontalIndex (Known K)) : (s (x*y)).horizontalPart j = (s x).horizontalPart j + (s y).horizontalPart j := by
    simp only [s,horizontal_at,Units.val_mul,order_mul _ x.ne_zero y.ne_zero]
  cases i with
  | centre c => exact hor (.inl c)
  | plus k i => exact (reg false k i).1
  | minus k i => exact (reg true k i).1
  | other j =>
    cases j with
    | horizontal i => exact hor (.inr i)
    | plusGuard k i => exact (reg false k i).2
    | minusGuard k i => exact (reg true k i).2
    | auxiliary k i =>
      have e (w : (RatFunc ℚ)ˣ) : (s w).auxiliary k i = branchOrder A T w.val false i.val :=
        (actual_aux A role _ _ _ _ k i).1
      change (s (x*y)).auxiliary k i = (s x).auxiliary k i + (s y).auxiliary k i
      rw [e,e,e,branch_mul]
    | auxiliaryGuard k i =>
      have e (w : (RatFunc ℚ)ˣ) : (s w).guards.auxiliary k i = branchOrder A T w.val true i.val :=
        (actual_aux A role _ _ _ _ k i).2
      change (s (x*y)).guards.auxiliary k i = (s x).guards.auxiliary k i + (s y).guards.auxiliary k i
      rw [e,e,e,branch_mul]
    | loneGuard i =>
      have e (w : (RatFunc ℚ)ˣ) : (s w).guards.lone i = branchOrder A T w.val true i.val :=
        actual_lone A role _ _ _ _ i
      change (s (x*y)).guards.lone i = (s x).guards.lone i + (s y).guards.lone i
      rw [e,e,e,branch_mul]

def primeUnit (q : PrimeIndex) : (RatFunc ℚ)ˣ := Units.mk0 (q.val : RatFunc ℚ) (Nat.cast_ne_zero.mpr q.property.ne_zero)

/-- All rational primes obey both finite mass equations, including primes
whose two old branch orders are nonzero. -/
theorem prime_mass (paired : ∀ p hp, (role p).isSome → (T p hp).paired) (q : PrimeIndex) :
    (signed A role T K (primeUnit q)).MassEquations (index A role) (sign A role) := by
  intro k
  let ht (c : Bool) := order (HorizontalOrders.valuation (centre c)) (primeUnit q).val
  have hz (c : Bool) : ht c = 0 := by
    change order _ (q.val : RatFunc ℚ) = 0
    rw [show (q.val : RatFunc ℚ) = RatFunc.C (q.val : ℚ) from (map_natCast _ _).symm,order,
      HorizontalOrders.valuation_constant _ _ (Nat.cast_ne_zero.mpr q.property.ne_zero)]
    simp
  change (preview A role ht _ _ _).signedMass _ _ k = (ht k : ℚ)
  rw [mass_eq,provisional_signedMass]
  have hsum : ∀ p ∈ A, discrepancy (role p) ht k (branchOrder A T (primeUnit q).val false p)
      (branchOrder A T (primeUnit q).val true p) = 0 := by
    intro p hp
    cases hr : role p with
    | none => rfl
    | some r =>
      have hfalse : MixedStageSelection.Active (T p hp).paired false := Or.inr (paired p hp (by simp [hr]))
      have htrue : MixedStageSelection.Active (T p hp).paired true := Or.inl rfl
      have hbr (b : Bool) (hb : MixedStageSelection.Active (T p hp).paired b) :
          branchOrder A T (primeUnit q).val b p = (q.val : ℚ_[p.val]).valuation := by
        simp only [branchOrder,hp,↓reduceDIte,branchValue,hb,primeUnit,Units.val_mk0,map_natCast]
      rw [hbr false hfalse,hbr true htrue]
      cases r <;> simp [discrepancy,forecastOrder,hz]
  rw [Finset.sum_eq_zero hsum,hz,hz,hz]
  norm_num

/-- The last raw is chosen only after both heights and every coarse guard
are known. Calibration of the named horizontals suffices for its coarse
factor to satisfy both equations. -/
theorem coarse_mass (hu : UniqueRegular A role) (paired : ∀ p hp, (role p).isSome → (T p hp).paired)
    (hh : ∀ i, (signed A role T K (horizontalUnit (horizontal K i))).MassEquations (index A role) (sign A role))
    (u : Profile (Aux A role) (Lone A role) (Known K)) :
    (signed A role T K (coarse A role T K u)).MassEquations (index A role) (sign A role) := by
  let S := Profile.massSubgroup (signed A role T K) (signed_values_mul A role T K hu) (index A role) (sign A role)
  change coarse A role T K u ∈ S
  unfold coarse coarseFactor weightedProduct Finsupp.prod
  simp only [Bool.false_eq_true,ite_false,one_mul]
  apply S.mul_mem
  · exact Subgroup.prod_mem _ fun i _ => S.zpow_mem (hh i) _
  · exact Subgroup.prod_mem _ fun p _ => S.zpow_mem (prime_mass A role T K paired p.val) _

end UnconditionalCounterexample.Variations.DyadicLedger.PrefixProfile
