import UnconditionalCounterexample.Variations.DyadicConcreteCoordinates
import UnconditionalCounterexample.Variations.DyadicMassReindex

/-! # The physical signed mass of each retained monic horizontal -/

noncomputable section
namespace UnconditionalCounterexample.Variations.DyadicLedger.Calibrated

open Polynomial GuardSupport Univariate FreezingCalendar OpeningCalibration Calibration
open DiscreteOrders DyadicDeviations WithZero
variable (a : Policy)

def massIndexing : MassReindex.Indexing PrimeIndex (Aux a) where
  role := (driver a).permanentRole
  regular c k n := regularPrime a (c,k,n)
  regular_iff p c k n := ⟨fun h => (driver a).permanent_regular_unique h
    (regularPrime_role a (c,k,n)), fun h => h ▸ regularPrime_role a (c,k,n)⟩
  auxiliary k := ⟨Aux.prime, by
    rintro ⟨p,i,e,h⟩ ⟨q,j,ε,h'⟩ he
    change p = q at he
    subst q
    rw [h] at h'
    cases h'
    rfl⟩
  index _ := Aux.index
  positive _ := Aux.positive
  auxiliary_iff p k i e := ⟨fun h => ⟨⟨p,i,e,h⟩,rfl,rfl,rfl⟩, by
    rintro ⟨j,rfl,rfl,rfl⟩
    exact j.role_eq⟩

private def branchOrder (f : Horizontal) (b : Bool) (p : PrimeIndex) : ℤ :=
  (aeval ((permanentSite (driver a).requirements p).branch b) f.val).valuation

private theorem primary_order (f : Horizontal) (p : PrimeIndex)
    (h : ((driver a).permanentRole p).isSome) :
    order (primaryVal a p h) (PrincipalProfiles.factor f) = branchOrder a f false p := by
  let s := permanentSite (driver a).requirements p
  let hb : MixedStageSelection.Active s.paired false := Or.inr (((driver a).paired_iff_role p).mpr h)
  have hn := (_root_.map_ne_zero (s.evaluate false hb)).mpr (PrincipalProfiles.factor_ne_zero f)
  change -log (Padic.mulValuation (s.evaluate false hb (PrincipalProfiles.factor f))) = _
  simp only [Padic.mulValuation_toFun, hn, ite_false, log_exp, neg_neg]
  exact congrArg Padic.valuation (ReturnTargets.evaluationHom_polynomial p.val _ _ f.val)

private theorem guard_order (f : Horizontal) (g : GuardIndex (Aux a) (Lone a)) :
    order (guardVal a g) (PrincipalProfiles.factor f) = branchOrder a f true (guardPrime a g) := by
  let R := (driver a).requirements
  let p := guardPrime a g
  let s := permanentSite R p
  have hn := (_root_.map_ne_zero (UnivariateExtraction.guardHom R p)).mpr (PrincipalProfiles.factor_ne_zero f)
  change -log (Padic.mulValuation (UnivariateExtraction.guardHom R p (PrincipalProfiles.factor f))) = _
  simp only [Padic.mulValuation_toFun, hn, ite_false, log_exp, neg_neg]
  rw [← UnivariateExtraction.eval_permanent_guard]
  exact congrArg Padic.valuation (ReturnTargets.evaluationHom_polynomial p.val _ _ f.val)

private theorem centre_factor (c : Bool) :
    (centre c).val = RegularForecast.centreFactor (if c then 1 else 0) := by
  cases c <;> simp [centre,zeroPoint,onePoint,RegularForecast.centreFactor]

private theorem physical_height (f : Horizontal) (p : Profile (Aux a) (Lone a) (Horiz a))
    (hv : ∀ i, p.signedValues i = order (valuation a i) (PrincipalProfiles.factor f)) :
    p.height = height f.val := by
  funext c
  change p.signedValues (.centre c) = _
  rw [hv]
  change order (HorizontalOrders.valuation (centre c)) (PrincipalProfiles.factor f) = _
  unfold height
  rw [← centre_factor]
  by_cases h : f = centre c
  · subst f
    simp [order]
  · have he : f.val ≠ (centre c).val := fun e => h (Subtype.ext e)
    simp [he,order,HorizontalOrders.valuation_factor_of_ne _ _ h]

private theorem physical_reads (f : Horizontal) (p : Profile (Aux a) (Lone a) (Horiz a))
    (hv : ∀ i, p.signedValues i = order (valuation a i) (PrincipalProfiles.factor f)) :
    MassReindex.Reads (massIndexing a) p (branchOrder a f false) (branchOrder a f true) where
  regular_primary c k i := by
    cases c with
    | false => exact ((hv (.plus k i)).trans (primary_order a f _ (by rw [regularPrime_role]; rfl))).symm
    | true => exact ((hv (.minus k i)).trans (primary_order a f _ (by rw [regularPrime_role]; rfl))).symm
  regular_guard c k i := by
    cases c with
    | false => exact ((hv (.other (.plusGuard k i))).trans (guard_order a f _)).symm
    | true => exact ((hv (.other (.minusGuard k i))).trans (guard_order a f _)).symm
  aux_primary k j := ((hv (.other (.auxiliary k j))).trans
    (primary_order a f j.prime (by rw [j.role_eq]; rfl))).symm
  aux_guard k j := ((hv (.other (.auxiliaryGuard k j))).trans (guard_order a f _)).symm

/-- A retained frozen horizontal has its two mass equations for the
valuation profile on actual permanent sites. -/
theorem retained_physical_mass (f : Horizontal)
    (hret : f.val ∉ Set.range (chain (driver a).requirements).raw)
    (p : Profile (Aux a) (Lone a) (Horiz a))
    (hv : ∀ i, p.signedValues i = order (valuation a i) (PrincipalProfiles.factor f)) :
    p.MassEquations (massIndexing a).index (massIndexing a).sign := by
  let D := driver a
  obtain hraw | ⟨t, ht, _⟩ := dispatcher_every_horizontal (planner a) f
  · exact (hret hraw).elim
  let b := max (t+1) (BulkInputs.scalarBound f)
  have hh := physical_height a f p hv
  intro k
  rw [MassReindex.signedMass_eq_sum (massIndexing a) (D.assigned b) p _ _ (physical_reads a f p hv)]
  · rw [hh]
    apply Eq.trans _ (permanent_mass a f ht (show t < b from (Nat.lt_succ_self _).trans_le (le_max_left _ _)) k)
    simp only [Driver.rationalMass, provisional_signedMass]
    congr 1
    apply Finset.sum_congr rfl
    intro pr hpr
    have hm : pr ∈ ((chain (driver a).requirements).approx b).state.assignment.primes := hpr
    simp only [Driver.rationalOrder,hm,↓reduceDIte,table_eq_permanentSite]
    rw [D.role_eq_permanent pr hpr]
    rfl
  · intro pr hpr r hr
    rw [hh]
    exact D.frozen_rational_orders_outside t f ht (predicts a f) pr hpr r hr

/-- At any paired fibre the two embeddings agree on every rational scalar,
including at primes dividing its numerator or denominator. -/
private theorem paired_scalar (q : ℚ) (p : PrimeIndex) (h : ((driver a).permanentRole p).isSome) :
    order (primaryVal a p h) (RatFunc.C q) =
      order (UnivariateExtraction.guardVal (driver a).requirements p) (RatFunc.C q) := by
  let s := permanentSite (driver a).requirements p
  let e := s.evaluate false (Or.inr (((driver a).paired_iff_role p).mpr h))
  let g := UnivariateExtraction.guardHom (driver a).requirements p
  have he : e.comp RatFunc.C = g.comp RatFunc.C := Subsingleton.elim _ _
  change -log (Padic.mulValuation (e (RatFunc.C q))) = -log (Padic.mulValuation (g (RatFunc.C q)))
  rw [show e (RatFunc.C q) = g (RatFunc.C q) from congrArg (fun u : ℚ →+* ℚ_[p.val] => u q) he]

theorem scalar_physical_mass (q : ℚ) (hq : q ≠ 0) (p : Profile (Aux a) (Lone a) (Horiz a))
    (hv : ∀ i, p.signedValues i = order (valuation a i) (RatFunc.C q)) :
    p.MassEquations (massIndexing a).index (massIndexing a).sign := by
  have hh (c : Bool) : p.height c = 0 := by
    change p.signedValues (.centre c) = 0
    rw [hv]
    change order (HorizontalOrders.valuation (centre c)) (RatFunc.C q) = 0
    rw [order, HorizontalOrders.valuation_constant _ _ hq]
    simp
  intro k
  have hp : p.plusDeviation k = p.guards.plus k := by
    ext i
    have he := (hv (.plus k i)).trans ((paired_scalar a q _ (by rw [regularPrime_role]; rfl)).trans
      (hv (.other (.plusGuard k i))).symm)
    simpa [Profile.signedValues,Profile.plus,hh] using he
  have hm : p.minusDeviation k = p.guards.minus k := by
    ext i
    have he := (hv (.minus k i)).trans ((paired_scalar a q _ (by rw [regularPrime_role]; rfl)).trans
      (hv (.other (.minusGuard k i))).symm)
    simpa [Profile.signedValues,Profile.minus,hh] using he
  have ha : p.auxiliary k = p.guards.auxiliary k := by
    ext j
    exact (hv (.other (.auxiliary k j))).trans
      ((paired_scalar a q j.prime (by rw [j.role_eq]; rfl)).trans (hv (.other (.auxiliaryGuard k j))).symm)
  simp [Profile.signedMass,Profile.regularMass,hh,hp,hm,ha]

end UnconditionalCounterexample.Variations.DyadicLedger.Calibrated
