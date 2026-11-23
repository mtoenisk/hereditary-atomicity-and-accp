import UnconditionalCounterexample.Variations.DyadicPrefixProfile
import UnconditionalCounterexample.Variations.DyadicSplitCoarse

/-!
# The coarse factor computed on the finite planning table

The selected horizontal factors form a finite signed product in ℚ(t). One
power of each already assigned rational prime then corrects its actual guard
order. Missing regular guard slots carry zero and require no prime choices.
-/

noncomputable section
namespace UnconditionalCounterexample.Variations.DyadicLedger.PrefixProfile
open Polynomial GuardSupport Univariate FreezingCalendar DiscreteOrders DyadicDeviations DyadicSplit

abbrev Known (K : Finset ℚ[X]) := {f : Horizontal // f.val ∈ K ∧ ∀ c, f ≠ centre c}

def horizontal (K : Finset ℚ[X]) : HorizontalIndex (Known K) → Horizontal
  | .inl c => centre c
  | .inr f => f.val

private theorem centre_injective : Function.Injective centre := by
  rintro (a|a) (b|b) h <;> first | rfl |
    (exfalso; have he := congrArg (fun f : Horizontal => f.val.eval 0) h
     norm_num [centre,zeroPoint,onePoint] at he)

theorem horizontal_injective (K : Finset ℚ[X]) : Function.Injective (horizontal K) := by
  rintro (c|i) (d|j) h
  · exact congrArg Sum.inl (centre_injective h)
  · exact False.elim (j.property.2 c h.symm)
  · exact False.elim (i.property.2 d h)
  · exact congrArg Sum.inr (Subtype.ext h)

variable (A : Finset PrimeIndex) (role : PrimeIndex → Option FibreRole) (T : Table A) (K : Finset ℚ[X])

/-- Read all horizontal orders on the frozen list, and both distinguished heights. -/
def signed (x : (RatFunc ℚ)ˣ) : Profile (Aux A role) (Lone A role) (Known K) :=
  fromTable A role T x.val ((PrincipalProfiles.exponents x.val x.ne_zero).subtypeDomain
    (fun f => f.val ∈ K ∧ ∀ c, f ≠ centre c))

theorem horizontal_at (x : (RatFunc ℚ)ˣ) (i : HorizontalIndex (Known K)) :
    (signed A role T K x).horizontalPart i = order (HorizontalOrders.valuation (horizontal K i)) x.val := by
  cases i with
  | inl c => rfl
  | inr f => exact (HorizontalOrders.neg_log_valuation_eq_exponents f.val x.val x.ne_zero).symm

/-- Slot in the typed guard family that corresponds to this actual finite prime. -/
def guardSlot (p : A) : GuardIndex (Aux A role) (Lone A role) :=
  match h : role p.val with
  | none => .inr (.inr (.inr ⟨p.val,p.property,h⟩))
  | some (.regular false k i) => .inl (k,i)
  | some (.regular true k i) => .inr (.inl (k,i))
  | some (.auxiliary k i e) => .inr (.inr (.inl ⟨k,⟨p.val,p.property,i,e,h⟩⟩))

private theorem slot_regular (p : A) (c k : Bool) (i : ℕ) (h : role p.val = some (.regular c k i)) :
    guardSlot A role p = (if c then .inr (.inl (k,i)) else .inl (k,i)) := by
  unfold guardSlot
  split <;> simp_all

private theorem slot_aux (k : Bool) (p : Aux A role k) (i : ℕ) (e : Bool)
    (h : role p.val = some (.auxiliary k i e)) :
    guardSlot A role ⟨p.val,p.property.1⟩ = .inr (.inr (.inl ⟨k,p⟩)) := by
  unfold guardSlot
  split <;> simp_all

  obtain ⟨rfl,rfl,rfl⟩ := h
  rfl

private theorem slot_lone (p : Lone A role) :
    guardSlot A role ⟨p.val,p.property.1⟩ = .inr (.inr (.inr p)) := by
  have h := p.property.2
  unfold guardSlot
  split <;> simp_all

def guardVal (p : A) := EvaluationDVR.valuation p.val.val ((T p.val p.property).evaluate true (Or.inl rfl))

theorem at_guard (hu : UniqueRegular A role) (x : (RatFunc ℚ)ˣ) (p : A) :
    (signed A role T K x).guardPart (guardSlot A role p) = order (guardVal A T p) x.val := by
  have hv : branchOrder A T x.val true p.val = order (guardVal A T p) x.val := by
    let e := (T p.val p.property).evaluate true (Or.inl rfl)
    have hn : e x.val ≠ 0 := (map_ne_zero e).mpr x.ne_zero
    have hb : MixedStageSelection.Active (T p.val p.property).paired true := Or.inl rfl
    rw [branchOrder,dite_eq_left p.property,DyadicSplit.branchValue,dite_eq_left hb]
    change (e x.val).valuation = -WithZero.log (Padic.mulValuation (e x.val))
    simp [Padic.mulValuation_toFun,hn]
  let ht (c : Bool) := order (HorizontalOrders.valuation (centre c)) x.val
  let ho := (PrincipalProfiles.exponents x.val x.ne_zero).subtypeDomain (fun f => f.val ∈ K ∧ ∀ c, f ≠ centre c)
  apply Eq.trans _ hv
  unfold guardSlot
  split
  · rename_i h
    exact actual_lone A role _ _ _ _ ⟨p.val,p.property,h⟩
  · rename_i k i h
    exact (actual_regular A role ht (branchOrder A T x.val false) (branchOrder A T x.val true) ho hu p.property h).2
  · rename_i k i h
    exact (actual_regular A role ht (branchOrder A T x.val false) (branchOrder A T x.val true) ho hu p.property h).2
  · rename_i k i e h
    exact (actual_aux A role ht (branchOrder A T x.val false) (branchOrder A T x.val true) ho k ⟨p.val,p.property,i,e,h⟩).2

variable (u : Profile (Aux A role) (Lone A role) (Known K))

def horizontalBase := weightedProduct (fun i => horizontalUnit (horizontal K i)) u.horizontalPart

def corrections : A →₀ ℤ := Finsupp.equivFunOnFinite.symm fun p =>
  u.guardPart (guardSlot A role p) - order (guardVal A T p) (horizontalBase A role K u : RatFunc ℚ)

def coarse := coarseFactor false (fun i => horizontalUnit (horizontal K i)) Subtype.val u.horizontalPart
  (corrections A role T K u)

private theorem singleton_sum {I : Type*} [DecidableEq I] (e : I →₀ ℤ) (i : I) :
    (e.sum fun j z => z * (if j = i then 1 else 0)) = e i := by
  classical
  by_cases h : i ∈ e.support <;> simp [Finsupp.sum,mul_ite,h,Finsupp.notMem_support_iff.mp]

theorem coarse_horizontal : (signed A role T K (coarse A role T K u)).horizontalPart = u.horizontalPart := by
  classical
  ext i
  rw [horizontal_at,coarse,coarseFactor_order]
  have hp (j : A) : order (HorizontalOrders.valuation (horizontal K i)) (j.val.val : RatFunc ℚ) = 0 := by
    rw [show (j.val.val : RatFunc ℚ) = RatFunc.C (j.val.val : ℚ) from (map_natCast _ _).symm,
      order,HorizontalOrders.valuation_constant _ _ (Nat.cast_ne_zero.mpr j.val.property.ne_zero)]
    simp
  have hh (j : HorizontalIndex (Known K)) :
      order (HorizontalOrders.valuation (horizontal K i)) (horizontalUnit (horizontal K j) : RatFunc ℚ) =
        if j = i then 1 else 0 := by
    change order _ (PrincipalProfiles.factor _) = _
    by_cases he : j=i
    · subst j; simp [order]
    · simp [order,HorizontalOrders.valuation_factor_of_ne _ _ (fun h => he (horizontal_injective K h)),he]
  simp [hp,hh]
  exact Eq.symm

theorem coarse_at_guard (hu : UniqueRegular A role) (p : A) :
    (signed A role T K (coarse A role T K u)).guardPart (guardSlot A role p) = u.guardPart (guardSlot A role p) := by
  classical
  rw [at_guard A role T K hu,coarse,coarseFactor_order]
  have hp (q : A) : order (guardVal A T p) (q.val.val : RatFunc ℚ) = if q = p then 1 else 0 := by
    let E := (T p.val p.property).evaluate true (Or.inl rfl)
    change order (EvaluationDVR.valuation p.val.val E) (q.val.val : RatFunc ℚ) = _
    by_cases h : q = p
    · subst q; simp [order]
    · have hn : q.val.val ≠ p.val.val := fun he => h (Subtype.ext (Subtype.ext he))
      simp [order,PairedResidues.valuation_prime_eq_one_of_ne q.val.val p.val.val E hn,h]
  simp only [hp,singleton_sum]
  rw [← weightedProduct_order]
  change order _ (horizontalBase A role K u : RatFunc ℚ) +
    (u.guardPart _ - order _ (horizontalBase A role K u : RatFunc ℚ)) = _
  omega

/-- A finite snapshot has no guard contributions at unallocated regular labels. -/
def Supported {H : Type*} (p : Profile (Aux A role) (Lone A role) H) : Prop :=
  ∀ c k i, (∀ q ∈ A, role q ≠ some (.regular c k i)) → regularGuard p c k i = 0

theorem signed_supported (x : (RatFunc ℚ)ˣ) : Supported A role (signed A role T K x) := by
  intro c k i hm
  let ht (c : Bool) := order (HorizontalOrders.valuation (centre c)) x.val
  let ho := (PrincipalProfiles.exponents x.val x.ne_zero).subtypeDomain (fun f => f.val ∈ K ∧ ∀ c, f ≠ centre c)
  exact (missing_regular A role ht (branchOrder A T x.val false) (branchOrder A T x.val true) ho hm).2

theorem split_supported {p u v : Profile (Aux A role) (Lone A role) (Known K)}
    {M : ℕ} (hs : SplitAt (index A role) (sign A role) p u v M) (hp : Supported A role p) :
    Supported A role u := by
  intro c k i hm
  have he := hp c k i hm
  cases c with
  | false =>
    have ht := hs.supplementary (.plusGuard k i)
    cases k <;> simp_all [regularGuard,Profile.signedValues,Supplement.channel]
  | true =>
    have ht := hs.supplementary (.minusGuard k i)
    cases k <;> simp_all [regularGuard,Profile.signedValues,Supplement.channel]

/-- All guard coordinates of the interpolated coarse factor, including zeros
on unassigned indices. -/
theorem coarse_guards (hu : UniqueRegular A role) (hs : Supported A role u) :
    (signed A role T K (coarse A role T K u)).guards = u.guards := by
  let b := signed A role T K (coarse A role T K u)
  have hb : Supported A role b := signed_supported A role T K _
  have reg (c k : Bool) (i : ℕ) : regularGuard b c k i = regularGuard u c k i := by
    by_cases ha : ∃ p ∈ A, role p = some (.regular c k i)
    · obtain ⟨p,hp,hr⟩ := ha
      have he := coarse_at_guard A role T K u hu ⟨p,hp⟩
      rw [slot_regular A role _ c k i hr] at he
      cases c <;> exact he
    · have hn := fun p (hp : p ∈ A) hr => ha ⟨p,hp,hr⟩
      exact (hb c k i hn).trans (hs c k i hn).symm
  apply Guards.ext_of_components (funext fun k => Finsupp.ext fun i => reg false k i)
    (funext fun k => Finsupp.ext fun i => reg true k i)
  · funext k
    ext i
    obtain ⟨j,e,hr⟩ := i.property.2
    have he := coarse_at_guard A role T K u hu ⟨i.val,i.property.1⟩
    rw [slot_aux A role k i j e hr] at he
    exact he
  · ext i
    have he := coarse_at_guard A role T K u hu ⟨i.val,i.property.1⟩
    rw [slot_lone A role i] at he
    exact he

end UnconditionalCounterexample.Variations.DyadicLedger.PrefixProfile
