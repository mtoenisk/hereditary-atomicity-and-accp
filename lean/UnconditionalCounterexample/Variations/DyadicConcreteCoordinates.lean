import UnconditionalCounterexample.Variations.DyadicCalibratedSites
import UnconditionalCounterexample.Variations.DyadicRationalLifts
import UnconditionalCounterexample.Variations.UnivariateExtraction

/-!
# The valuation coordinates of the calibrated selector

All regular and auxiliary indices point at actual permanently assigned primes.
Every rational prime contributes exactly one guard. The horizontal coordinates
consist of the two centres and the remaining retained monic irreducibles.
-/

noncomputable section
namespace UnconditionalCounterexample.Variations.DyadicLedger.Calibrated
open GuardSupport Univariate FreezingCalendar DiscreteOrders DyadicDeviations WithZero

variable (a : Policy)

structure Aux (k : Bool) where
  prime : PrimeIndex
  index : ℕ
  positive : Bool
  role_eq : (driver a).permanentRole prime = some (.auxiliary k index positive)

abbrev Lone := {p : PrimeIndex // (driver a).permanentRole p = none}

def centre : Bool → Horizontal
  | false => zeroPoint
  | true => onePoint

abbrev Horiz := {q : Horizontal // q.val ∉ Set.range (chain (driver a).requirements).raw ∧
  ∀ c, q ≠ centre c}

abbrev Coordinates := DyadicProfiles.Site (Supplement (Aux a) (Lone a) (Horiz a))

def horizontal : HorizontalIndex (Horiz a) → Horizontal
  | .inl c => centre c
  | .inr h => h.val

private theorem centre_injective : Function.Injective centre := by
  rintro (a|b) (c|d) h <;> first | rfl |
    (exfalso; have hh := congrArg (fun f : Horizontal => f.val.eval 0) h;
     norm_num [centre,zeroPoint,onePoint] at hh)

theorem horizontal_injective : Function.Injective (horizontal a) := by
  rintro (c|i) (d|j) h
  · exact congrArg Sum.inl (centre_injective h)
  · exact False.elim (j.property.2 c h.symm)
  · exact False.elim (i.property.2 d h)
  · exact congrArg Sum.inr (Subtype.ext h)

def toPrime : GuardIndex (Aux a) (Lone a) → PrimeIndex
  | .inl (k,i) => regularPrime a (false,k,i)
  | .inr (.inl (k,i)) => regularPrime a (true,k,i)
  | .inr (.inr (.inl ⟨_,j⟩)) => j.prime
  | .inr (.inr (.inr g)) => g.val

def ofPrime (p : PrimeIndex) : GuardIndex (Aux a) (Lone a) :=
  match h : (driver a).permanentRole p with
  | none => .inr (.inr (.inr ⟨p,h⟩))
  | some (.regular false k i) => .inl (k,i)
  | some (.regular true k i) => .inr (.inl (k,i))
  | some (.auxiliary k i e) => .inr (.inr (.inl ⟨k,p,i,e,h⟩))

theorem toPrime_ofPrime (p : PrimeIndex) : toPrime a (ofPrime a p) = p := by
  unfold ofPrime
  split
  · rfl
  · exact (driver a).permanent_regular_unique (regularPrime_role a _) ‹_›
  · exact (driver a).permanent_regular_unique (regularPrime_role a _) ‹_›
  · rfl

theorem ofPrime_toPrime (g : GuardIndex (Aux a) (Lone a)) : ofPrime a (toPrime a g) = g := by
  rcases g with ⟨k,i⟩ | ⟨k,i⟩ | ⟨k,⟨p,i,e,h⟩⟩ | ⟨p,h⟩
  · unfold ofPrime
    split <;> rename_i he <;> simp only [toPrime,regularPrime_role] at he <;> cases he
    rfl
  · unfold ofPrime
    split <;> rename_i he <;> simp only [toPrime,regularPrime_role] at he <;> cases he
    rfl
  · unfold ofPrime
    split <;> rename_i he <;> change (driver a).permanentRole p = _ at he <;> rw [h] at he <;> cases he
    rfl
  · unfold ofPrime
    split <;> rename_i he <;> change (driver a).permanentRole p = _ at he <;> rw [h] at he <;> cases he
    rfl

def guardPrime : GuardIndex (Aux a) (Lone a) ≃ PrimeIndex :=
  ⟨toPrime a,ofPrime a,ofPrime_toPrime a,toPrime_ofPrime a⟩

def primaryVal (p : PrimeIndex) (h : ((driver a).permanentRole p).isSome) :
    Valuation (RatFunc ℚ) ℤᵐ⁰ :=
  EvaluationDVR.valuation p.val ((permanentSite (driver a).requirements p).evaluate false
    (Or.inr (((driver a).paired_iff_role p).mpr h)))

def regularVal (l : RegularLabel) := primaryVal a (regularPrime a l) (by rw [regularPrime_role]; rfl)

def auxVal (k : Bool) (j : Aux a k) := primaryVal a j.prime (by rw [j.role_eq]; rfl)

abbrev guardVal (g : GuardIndex (Aux a) (Lone a)) :=
  UnivariateExtraction.guardVal (driver a).requirements (guardPrime a g)

def valuation : Coordinates a → Valuation (RatFunc ℚ) ℤᵐ⁰
  | .centre c => HorizontalOrders.valuation (centre c)
  | .plus k i => regularVal a (false,k,i)
  | .minus k i => regularVal a (true,k,i)
  | .other (.auxiliary k j) => auxVal a k j
  | .other (.plusGuard k i) => guardVal a (.inl (k,i))
  | .other (.minusGuard k i) => guardVal a (.inr (.inl (k,i)))
  | .other (.auxiliaryGuard k j) => guardVal a (.inr (.inr (.inl ⟨k,j⟩)))
  | .other (.loneGuard g) => guardVal a (.inr (.inr (.inr g)))
  | .other (.horizontal q) => HorizontalOrders.valuation q.val

theorem valuation_horizontal (i : HorizontalIndex (Horiz a)) :
    valuation a (horizontalSite i) = HorizontalOrders.valuation (horizontal a i) := by cases i <;> rfl

theorem valuation_guard (i : GuardIndex (Aux a) (Lone a)) :
    valuation a (guardSite i) = guardVal a i := by rcases i with ⟨k,j⟩ | ⟨k,j⟩ | ⟨k,j⟩ | j <;> rfl

end UnconditionalCounterexample.Variations.DyadicLedger.Calibrated
