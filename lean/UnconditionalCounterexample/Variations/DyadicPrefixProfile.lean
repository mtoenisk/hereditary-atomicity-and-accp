import UnconditionalCounterexample.HorizontalOrders
import UnconditionalCounterexample.Variations.DyadicRoundCalibration
import UnconditionalCounterexample.Variations.DyadicSplitCoefficients

/-!
# Finite profiles for planning the next dyadic split

On an assigned finite table, only genuine auxiliary primes index auxiliary
columns. The two regular tails are supplied by the horizontal heights. A
missing regular site has its tail value and a missing regular guard has
order zero. The signed mass agrees with that of the calibration table.
-/

noncomputable section
namespace UnconditionalCounterexample.Variations.DyadicLedger.PrefixProfile

open Polynomial GuardSupport Calibration DyadicDeviations DyadicColumns Univariate

attribute [local instance] Classical.propDecidable

variable (A : Finset PrimeIndex) (role : PrimeIndex → Option FibreRole)

def IsAux (k : Bool) (p : PrimeIndex) : Prop :=
  p ∈ A ∧ ∃ i e, role p = some (.auxiliary k i e)

abbrev Aux (k : Bool) := {p : PrimeIndex // IsAux A role k p}

abbrev Lone := {p : PrimeIndex // p ∈ A ∧ role p = none}

def prime : (Σ k, Aux A role k) ↪ PrimeIndex where
  toFun j := j.2.val
  inj' := by
    rintro ⟨k,⟨p,hp⟩⟩ ⟨l,⟨q,hq⟩⟩ he
    change p = q at he
    subst q
    obtain ⟨i,e,hi⟩ := hp.2
    obtain ⟨j,d,hj⟩ := hq.2
    obtain rfl := (FibreRole.auxiliary.inj (Option.some.inj (hi.symm.trans hj))).1
    rfl

def index (k : Bool) (i : Aux A role k) := auxWeight role k i.val

def positive (k : Bool) (i : Aux A role k) : Bool := decide (auxSign role k i.val = 1)

def sign (k : Bool) (i : Aux A role k) := auxSign role k i.val

theorem sign_eq (k : Bool) (i : Aux A role k) :
    sign A role k i = if positive A role k i then 1 else -1 := by
  obtain ⟨j,e,h⟩ := i.property.2
  cases e <;> simp [sign,positive,auxSign,h,FibreRole.sign]

variable {H : Type*} (height : Bool → ℤ) (primary guard : PrimeIndex → ℤ) (horizontal : H →₀ ℤ)

/-- The full finite snapshot, with the actual labels at assigned fibres. -/
def preview : Profile (Aux A role) (Lone A role) H :=
  let v := provisionalProfile A role height primary guard horizontal
  { height := height
    plusDeviation := v.plusDeviation
    minusDeviation := v.minusDeviation
    guards := {
      plus := v.guards.plus
      minus := v.guards.minus
      auxiliary k := (v.guards.auxiliary k).subtypeDomain (IsAux A role k)
      lone := v.guards.lone.subtypeDomain (fun p => p ∈ A ∧ role p = none) }
    auxiliary k := (v.auxiliary k).subtypeDomain (IsAux A role k)
    horizontal := horizontal }

private theorem aux_value (values : PrimeIndex → ℤ) (p : PrimeIndex) (k : Bool) :
    (∑ q ∈ A, auxiliaryRow (role q) q k (values q)) p = if IsAux A role k p then values p else 0 := by
  classical
  have haway (q : PrimeIndex) (h : q ≠ p) : auxiliaryRow (role q) q k (values q) p = 0 := by
    cases hrole : role q with
    | none => rfl
    | some r =>
      cases r with
      | regular => rfl
      | auxiliary l i e => by_cases he : l=k <;> simp [auxiliaryRow,he,h]
  rw [Finsupp.finsetSum_apply]
  by_cases hp : p ∈ A
  · rw [Finset.sum_eq_single_of_mem p hp (fun q _ h => haway q h)]
    cases hr : role p with
    | none => simp [IsAux,hp,hr,auxiliaryRow]
    | some r =>
      cases r with
      | regular => simp [IsAux,hp,hr,auxiliaryRow]
      | auxiliary l i e => by_cases h : l=k <;> simp [IsAux,hp,hr,auxiliaryRow,h]
  · rw [Finset.sum_eq_zero (fun q hq => haway q (fun he => hp (he ▸ hq)))]
    simp [IsAux,hp]

/-- Reindexing the two finite auxiliary rows removes only zero entries. -/
theorem mass_eq (k : Bool) :
    (preview A role height primary guard horizontal).signedMass (index A role) (sign A role) k =
    (provisionalProfile A role height primary guard horizontal).signedMass (auxWeight role) (auxSign role) k := by
  classical
  let x := (provisionalProfile A role height primary guard horizontal).auxiliary k
  let y := (provisionalProfile A role height primary guard horizontal).guards.auxiliary k
  have support : ∀ p ∈ (x-y).support, IsAux A role k p := by
    intro p hp
    by_contra h
    have hv := Finsupp.mem_support_iff.mp hp
    change x p - y p ≠ 0 at hv
    simp only [x,y,provisionalProfile,aux_value, h,ite_false,sub_self,ne_self_iff_false] at hv
  simp only [Profile.signedMass, mass_auxiliaryTransfer]
  congr 1
  change (((x.subtypeDomain (IsAux A role k))-(y.subtypeDomain (IsAux A role k))).sum _) = (x-y).sum _
  rw [← Finsupp.subtypeDomain_sub]
  exact Finsupp.sum_subtypeDomain_index (h := fun p (v : ℤ) =>
    ((v * auxSign role k p : ℤ) : ℚ) * (1/2 : ℚ) ^ (auxWeight role k p+1)) support

theorem actual_aux (k : Bool) (i : Aux A role k) :
    (preview A role height primary guard horizontal).auxiliary k i = primary i.val ∧
      (preview A role height primary guard horizontal).guards.auxiliary k i = guard i.val := by
  change (∑ q ∈ A, auxiliaryRow (role q) q k (primary q)) i.val = _ ∧
    (∑ q ∈ A, auxiliaryRow (role q) q k (guard q)) i.val = _
  simp [aux_value,i.property]

theorem actual_lone (i : Lone A role) : (preview A role height primary guard horizontal).guards.lone i = guard i.val := by
  classical
  change (∑ p ∈ A, if (role p).isNone then Finsupp.single p (guard p) else 0) i.val = _
  rw [Finsupp.finsetSum_apply,Finset.sum_eq_single_of_mem i.val i.property.1]
  · simp [i.property.2]
  · intro p _ hn
    split <;> simp [hn]

private theorem regularRow_at (r : Option FibreRole) (c k : Bool) (i : ℕ) (z : ℤ) :
    regularRow r c k z i = if r = some (.regular c k i) then z else 0 := by
  cases r with
  | none => rfl
  | some r =>
    cases r with
    | auxiliary => rfl
    | regular a b j =>
      by_cases h : a=c ∧ b=k
      · obtain ⟨rfl,rfl⟩ := h
        by_cases he : j=i <;> simp [regularRow,he]
      · simp [regularRow,h]
        aesop

/-- At most one prime owns each regular label in the finite prefix. -/
def UniqueRegular := ∀ p ∈ A, ∀ q ∈ A, ∀ c k i,
  role p = some (.regular c k i) → role q = some (.regular c k i) → p=q

private theorem reg_at (hu : UniqueRegular A role) (values : PrimeIndex → ℤ)
    {c k : Bool} {i : ℕ} {p : PrimeIndex} (hp : p ∈ A) (hr : role p = some (.regular c k i)) :
    (∑ q ∈ A, regularRow (role q) c k (values q)) i = values p := by
  rw [Finsupp.finsetSum_apply,Finset.sum_eq_single_of_mem p hp]
  · simp [regularRow_at,hr]
  · intro q hq hn
    rw [regularRow_at,ite_eq_right (fun he => hn (hu q hq p hp c k i he hr))]

private theorem reg_missing (values : PrimeIndex → ℤ) {c k : Bool} {i : ℕ}
    (h : ∀ p ∈ A, role p ≠ some (.regular c k i)) :
    (∑ q ∈ A, regularRow (role q) c k (values q)) i = 0 := by
  rw [Finsupp.finsetSum_apply]
  exact Finset.sum_eq_zero fun q hq => by rw [regularRow_at,ite_eq_right (h q hq)]

def regularValue {J : Bool → Type*} {G H : Type*} (p : Profile J G H) (c k : Bool) (i : ℕ) : ℤ :=
  if c then p.minus k i else p.plus k i

def regularGuard {J : Bool → Type*} {G H : Type*} (p : Profile J G H) (c k : Bool) (i : ℕ) : ℤ :=
  if c then p.guards.minus k i else p.guards.plus k i

theorem actual_regular (hu : UniqueRegular A role) {p : PrimeIndex} (hp : p ∈ A) {c k : Bool} {i : ℕ}
    (hr : role p = some (.regular c k i)) :
    let v := preview A role height primary guard horizontal
    regularValue v c k i = primary p ∧ regularGuard v c k i = guard p := by
  have h₁ := reg_at A role hu (fun q => primary q - height c) hp hr
  have h₂ := reg_at A role hu guard hp hr
  have sum := (congrArg (height c + ·) h₁).trans (show height c + (primary p-height c) = primary p by omega)
  cases c <;> exact ⟨sum,h₂⟩

theorem missing_regular {c k : Bool} {i : ℕ} (miss : ∀ p ∈ A, role p ≠ some (.regular c k i)) :
    let v := preview A role height primary guard horizontal
    regularValue v c k i = height c ∧ regularGuard v c k i = 0 := by
  have h₁ := reg_missing A role (fun q => primary q - height c) miss
  have h₂ := reg_missing A role guard miss
  cases c <;> exact ⟨(congrArg (_ + ·) h₁).trans (add_zero _),h₂⟩

/-- Nonnegativity at the two centres and the actually assigned fibres is
enough to test the entire infinite preview for effectiveness. -/
theorem effective (hu : UniqueRegular A role) (hh : ∀ c, 0 ≤ height c)
    (hp : ∀ p ∈ A, (role p).isSome → 0 ≤ primary p) (hg : ∀ p ∈ A, 0 ≤ guard p)
    (hhoriz : ∀ i, 0 ≤ horizontal i) :
    ∀ i, 0 ≤ (preview A role height primary guard horizontal).signedValues i := by
  let v := preview A role height primary guard horizontal
  have reg (c k : Bool) (i : ℕ) : 0 ≤ regularValue v c k i ∧ 0 ≤ regularGuard v c k i := by
    by_cases h : ∃ p ∈ A, role p = some (.regular c k i)
    · obtain ⟨p,hm,hr⟩ := h
      obtain ⟨he,he'⟩ := actual_regular A role height primary guard horizontal hu hm hr
      exact ⟨he ▸ hp p hm (by simp [hr]), he' ▸ hg p hm⟩
    · obtain ⟨he,he'⟩ := missing_regular A role height primary guard horizontal
        (c := c) (k := k) (i := i) (fun p hmem hr => h ⟨p,hmem,hr⟩)
      exact ⟨he ▸ hh c, he' ▸ le_rfl⟩
  intro i
  cases i with
  | centre c => exact hh c
  | plus k i => exact (reg false k i).1
  | minus k i => exact (reg true k i).1
  | other t =>
    cases t with
    | plusGuard k i => exact (reg false k i).2
    | minusGuard k i => exact (reg true k i).2
    | auxiliary k i =>
      obtain ⟨_,_,hr⟩ := i.property.2
      change 0 ≤ (preview A role height primary guard horizontal).auxiliary k i
      rw [(actual_aux A role height primary guard horizontal k i).1]
      exact hp i.val i.property.1 (by simp [hr])
    | auxiliaryGuard k i =>
      change 0 ≤ (preview A role height primary guard horizontal).guards.auxiliary k i
      rw [(actual_aux A role height primary guard horizontal k i).2]
      exact hg i.val i.property.1
    | loneGuard i =>
      change 0 ≤ (preview A role height primary guard horizontal).guards.lone i
      rw [actual_lone]
      exact hg i.val i.property.1
    | horizontal i => exact hhoriz i

/-- An actual finite table supplies these two value rows even where no
primary is present. The primary row is used only by paired roles. -/
def branchOrder (T : Table A) (x : RatFunc ℚ) (b : Bool) (p : PrimeIndex) : ℤ :=
  if hp : p ∈ A then (DyadicSplit.branchValue (T p hp) b x).valuation else 0

def centre : Bool → FreezingCalendar.Horizontal
  | false => FreezingCalendar.zeroPoint
  | true => FreezingCalendar.onePoint

def fromTable (T : Table A) (x : RatFunc ℚ) (horizontal : H →₀ ℤ) :=
  preview A role (fun c => DiscreteOrders.order (HorizontalOrders.valuation (centre c)) x)
    (branchOrder A T x false) (branchOrder A T x true) horizontal

end UnconditionalCounterexample.Variations.DyadicLedger.PrefixProfile
