import UnconditionalCounterexample.Variations.DyadicColumnLifting
import UnconditionalCounterexample.Variations.DyadicPair
import UnconditionalCounterexample.DiscreteOrders

/-!
# Dyadic profiles on an intersection of discrete valuation rings

Index all the defining horizontal and vertical valuations in the common field.
An integral element gives an effective regular profile, and divisibility follows
from the actual valuation rings. A rational-function lift of a pure effective
profile lies in this intersection automatically.
-/

noncomputable section

namespace UnconditionalCounterexample.DyadicDeviations

open DyadicProfiles (Site)

/-- Sites outside the regular evaluations and the two centres. -/
inductive Supplement (J : Bool → Type*) (G H : Type*) where
  | auxiliary (k : Bool) (j : J k)
  | plusGuard (k : Bool) (n : ℕ)
  | minusGuard (k : Bool) (n : ℕ)
  | auxiliaryGuard (k : Bool) (j : J k)
  | loneGuard (g : G)
  | horizontal (h : H)

variable {J : Bool → Type*} {G H : Type*}

theorem Guards.ext_of_components {p q : Guards J G} (h₁ : p.plus = q.plus) (h₂ : p.minus = q.minus)
    (h₃ : p.auxiliary = q.auxiliary) (h₄ : p.lone = q.lone) : p = q := by
  cases p
  cases q
  simp_all

namespace Profile

/-- All additive coordinates, indexed by the same sites as the actual valuations. -/
def signedValues (p : Profile J G H) : Site (Supplement J G H) → ℤ
  | .centre k => p.height k
  | .plus k n => p.plus k n
  | .minus k n => p.minus k n
  | .other (.auxiliary k j) => p.auxiliary k j
  | .other (.plusGuard k n) => p.guards.plus k n
  | .other (.minusGuard k n) => p.guards.minus k n
  | .other (.auxiliaryGuard k j) => p.guards.auxiliary k j
  | .other (.loneGuard g) => p.guards.lone g
  | .other (.horizontal h) => p.horizontal h

theorem signedValues_injective : Function.Injective (signedValues (J := J) (G := G) (H := H)) := by
  intro p q h
  have heights : p.height = q.height := funext fun k => congrFun h (.centre k)
  apply Profile.ext heights
  · ext k n
    have hv := congrFun h (.plus k n)
    simpa [signedValues, plus, heights] using hv
  · ext k n
    have hv := congrFun h (.minus k n)
    simpa [signedValues, minus, heights] using hv
  · ext k j
    exact congrFun h (.other (.auxiliary k j))
  · have hplus : p.guards.plus = q.guards.plus := by
      ext k n
      exact congrFun h (.other (.plusGuard k n))
    have hminus : p.guards.minus = q.guards.minus := by
      ext k n
      exact congrFun h (.other (.minusGuard k n))
    have haux : p.guards.auxiliary = q.guards.auxiliary := by
      ext k j
      exact congrFun h (.other (.auxiliaryGuard k j))
    have hlone : p.guards.lone = q.guards.lone := by
      ext g
      exact congrFun h (.other (.loneGuard g))
    exact Guards.ext_of_components hplus hminus haux hlone
  · ext h'
    exact congrFun h (.other (.horizontal h'))

theorem signedValues_ofRegular (p : DyadicProfiles.Profile) (i : Site (Supplement J G H)) :
    (ofRegular p).signedValues i = ((p.values 0 i : ℕ) : ℤ) := by
  cases i with
  | centre k => rfl
  | plus k n =>
    change (p.height false : ℤ) + ((p.plus k n : ℤ) - p.height false) = _
    simp [DyadicProfiles.Profile.values]
  | minus k n =>
    change (p.height true : ℤ) + ((p.minus k n : ℤ) - p.height true) = _
    simp [DyadicProfiles.Profile.values]
  | other i => cases i <;> rfl

private def regularSupport (p : Profile J G H) : Finset ℕ :=
  Finset.univ.biUnion fun k => (p.plusDeviation k).support ∪ (p.minusDeviation k).support

private theorem deviations_vanish (p : Profile J G H) (k : Bool) {n : ℕ}
    (hn : p.regularSupport.sup id + 1 ≤ n) :
    p.plusDeviation k n = 0 ∧ p.minusDeviation k n = 0 := by
  have hout : n ∉ p.regularSupport := fun h =>
    (Nat.not_lt_of_le (Finset.le_sup (f := id) h)) hn
  constructor <;> by_contra he
  · exact hout (Finset.mem_biUnion.mpr ⟨k, Finset.mem_univ _, Finset.mem_union_left _
      (Finsupp.mem_support_iff.mpr he)⟩)
  · exact hout (Finset.mem_biUnion.mpr ⟨k, Finset.mem_univ _, Finset.mem_union_right _
      (Finsupp.mem_support_iff.mpr he)⟩)

/-- Natural regular valuations with an explicit common cutoff for both channels. -/
def natRegular (p : Profile J G H) : DyadicProfiles.Profile where
  height k := (p.height k).toNat
  plus k n := (p.plus k n).toNat
  minus k n := (p.minus k n).toNat
  cutoff := p.regularSupport.sup id + 1
  plus_stable k _ hn := by simp [plus, (deviations_vanish p k hn).1]
  minus_stable k _ hn := by simp [minus, (deviations_vanish p k hn).2]

def natExtra (p : Profile J G H) (i : Supplement J G H) : ℕ := (p.signedValues (.other i)).toNat

theorem natRegular_values (p : Profile J G H) (i : Site (Supplement J G H)) :
    p.natRegular.values p.natExtra i = (p.signedValues i).toNat := by cases i <;> rfl

theorem eq_ofRegular_of_pure (p : Profile J G H) (hn : ∀ i, 0 ≤ p.signedValues i)
    (hextra : p.natExtra = 0) : p = ofRegular p.natRegular := by
  apply signedValues_injective
  funext i
  rw [signedValues_ofRegular, ← hextra, natRegular_values, Int.toNat_of_nonneg (hn i)]

/-- Supplementary coordinates have finite support, also after passing to
effective values. Both infinite regular tails are excluded from these sites. -/
theorem finite_natExtra (p : Profile J G H) : (Function.support p.natExtra).Finite := by
  classical
  let S : Finset (Supplement J G H) :=
    Finset.univ.biUnion (fun k =>
      ((p.auxiliary k).support.image (Supplement.auxiliary k) ∪
        (p.guards.plus k).support.image (Supplement.plusGuard k)) ∪
      ((p.guards.minus k).support.image (Supplement.minusGuard k) ∪
        (p.guards.auxiliary k).support.image (Supplement.auxiliaryGuard k))) ∪
    (p.guards.lone.support.image Supplement.loneGuard ∪
      p.horizontal.support.image Supplement.horizontal)
  apply S.finite_toSet.subset
  intro i hi
  have hvalue : p.signedValues (.other i) ≠ 0 := fun h =>
    hi (show p.natExtra i = 0 by simp [natExtra, h])
  cases i with
  | loneGuard g =>
    exact Finset.mem_union_right _ (Finset.mem_union_left _ (Finset.mem_image.mpr
      ⟨g, Finsupp.mem_support_iff.mpr hvalue, rfl⟩))
  | horizontal j =>
    exact Finset.mem_union_right _ (Finset.mem_union_right _ (Finset.mem_image.mpr
      ⟨j, Finsupp.mem_support_iff.mpr hvalue, rfl⟩))
  | auxiliary k j | plusGuard k j | minusGuard k j | auxiliaryGuard k j =>
    apply Finset.mem_union_left
    apply Finset.mem_biUnion.mpr
    refine ⟨k, Finset.mem_univ _, ?_⟩
    simp only [Finset.mem_union]
    first
    | exact Or.inl (Or.inl (Finset.mem_image.mpr ⟨j, Finsupp.mem_support_iff.mpr hvalue, rfl⟩))
    | exact Or.inl (Or.inr (Finset.mem_image.mpr ⟨j, Finsupp.mem_support_iff.mpr hvalue, rfl⟩))
    | exact Or.inr (Or.inl (Finset.mem_image.mpr ⟨j, Finsupp.mem_support_iff.mpr hvalue, rfl⟩))
    | exact Or.inr (Or.inr (Finset.mem_image.mpr ⟨j, Finsupp.mem_support_iff.mpr hvalue, rfl⟩))

theorem translate_difference (p q : Profile J G H) (index : (k : Bool) → J k → ℕ)
    (sign : (k : Bool) → J k → ℤ) (e : Columns J) (i : Site (Supplement J G H)) :
    (p.translate index sign e).signedValues i - p.signedValues i =
      (q.translate index sign e).signedValues i - q.signedValues i := by
  cases i with
  | centre k => simp [signedValues, translate, addColumns]
  | plus k n => simp [signedValues, translate, addColumns, plus]; abel
  | minus k n => simp [signedValues, translate, addColumns, minus]
  | other j => cases j <;> simp [signedValues, translate, addColumns]

end Profile

open DiscreteOrders WithZero

variable {F : Type*} [Field F]
variable (v : Site (Supplement J G H) → Valuation F ℤᵐ⁰)
variable (signed : Fˣ → Profile J G H)
variable (hval : ∀ (u : Fˣ) i, (signed u).signedValues i = order (v i) (u : F))

/-- At zero choose the same signed profile as at one, in accordance with the
zero convention for `DiscreteOrders.order`. -/
private def fieldUnit (z : F) : Fˣ := by
  classical
  exact if h : z = 0 then 1 else Units.mk0 z h

private def profileAt (x : fullIntersection v) : Profile J G H :=
  signed (fieldUnit (x : F))

include hval in
private theorem values_at (x : fullIntersection v) (i : Site (Supplement J G H)) :
    (profileAt v signed x).signedValues i = order (v i) (x : F) := by
  rw [profileAt, hval]
  by_cases h : (x : F) = 0 <;> simp [fieldUnit, h]

include hval in
private theorem nat_values_at (x : fullIntersection v) (i : Site (Supplement J G H)) :
    (profileAt v signed x).natRegular.values (profileAt v signed x).natExtra i =
      natOrder (v i) (x : F) := by
  rw [Profile.natRegular_values, values_at v signed hval]
  rfl

/-- Valuation laws supply multiplication and divisibility on the literal full
intersection. The inputs from selection are the two signed mass equations,
the actual signed values of field elements, and lifts of compatible targets. -/
def intersectionRealization
    (index : (k : Bool) → J k → ℕ) (sign : (k : Bool) → J k → ℤ)
    (hmass : ∀ u, (signed u).MassEquations index sign)
    (hlift : ∀ t : Profile J G H, t.MassEquations index sign → ∃ u, signed u = t) :
    DyadicProfiles.Realization (fullIntersection v) (Supplement J G H) where
  regular x := (profileAt v signed x).natRegular
  extra x := (profileAt v signed x).natExtra
  mul_values a b ha hb := by
    funext i
    simp only [Pi.add_apply, nat_values_at v signed hval]
    exact natOrder_mul (v i) (fun h => ha (Subtype.ext h)) (fun h => hb (Subtype.ext h))
      (integral v a i) (integral v b i)
  dvd_iff a b ha hb := by
    rw [dvd_iff_natOrder_le v ha hb]
    apply forall_congr'
    intro i
    rw [nat_values_at v signed hval, nat_values_at v signed hval]
  mass_of_pure a ha hzero := by
    let p := profileAt v signed a
    have hpure : p = Profile.ofRegular p.natRegular := by
      apply p.eq_ofRegular_of_pure _ hzero
      intro i
      rw [show p.signedValues i = order (v i) (a : F) from values_at v signed hval a i]
      exact (order_nonneg_iff (v i) (fun h => ha (Subtype.ext h))).mpr (integral v a i)
    intro k
    have he := hmass (fieldUnit (a : F)) k
    change p.signedMass index sign k = (p.height k : ℚ) at he
    rw [hpure, Profile.signedMass_ofRegular] at he
    exact_mod_cast he
  realize t ht := by
    let target : Profile J G H := Profile.ofRegular t
    have htarget : target.MassEquations index sign := by
      intro k
      rw [show target.signedMass index sign k = t.signedMass k from
        Profile.signedMass_ofRegular t index sign k, ht k]
      simp [target, Profile.ofRegular]
    obtain ⟨u, hu⟩ := hlift target htarget
    have huord (i) : order (v i) (u : F) = ((t.values (0 : Supplement J G H → ℕ) i : ℕ) : ℤ) := by
      rw [← hval, hu]
      exact Profile.signedValues_ofRegular t i
    have hmem : (u : F) ∈ fullIntersection v := by
      apply (IntersectionDomain.mem_intersection ⊤ v _).mpr
      refine ⟨Subring.mem_top _, fun i => (order_nonneg_iff (v i) u.ne_zero).mp ?_⟩
      rw [huord]
      exact Int.natCast_nonneg _
    let a : fullIntersection v := ⟨(u : F), hmem⟩
    refine ⟨a, (fun h => u.ne_zero (congrArg Subtype.val h)), ?_⟩
    funext i
    rw [nat_values_at v signed hval]
    change (order (v i) (u : F)).toNat = _
    rw [huord, Int.toNat_natCast]

section IntersectionCoordinates

variable (index : (k : Bool) → J k → ℕ) (sign : (k : Bool) → J k → ℤ)
    (hmass : ∀ u, (signed u).MassEquations index sign)
    (hlift : ∀ t : Profile J G H, t.MassEquations index sign → ∃ u, signed u = t)

theorem intersectionRealization_regular (x : fullIntersection v) (hx : (x : F) ≠ 0) :
    (intersectionRealization v signed hval index sign hmass hlift).regular x =
      (signed (Units.mk0 (x : F) hx)).natRegular := by
  change (profileAt v signed x).natRegular = _
  simp [profileAt, fieldUnit, hx]

theorem intersectionRealization_extra (x : fullIntersection v) (hx : (x : F) ≠ 0) :
    (intersectionRealization v signed hval index sign hmass hlift).extra x =
      (signed (Units.mk0 (x : F) hx)).natExtra := by
  change (profileAt v signed x).natExtra = _
  simp [profileAt, fieldUnit, hx]

theorem intersectionRealization_values (x : fullIntersection v) (i : Site (Supplement J G H)) :
    (intersectionRealization v signed hval index sign hmass hlift).values x i =
      natOrder (v i) (x : F) := nat_values_at v signed hval x i

theorem intersectionRealization_finite_extra (x : fullIntersection v) :
    (Function.support ((intersectionRealization v signed hval index sign hmass hlift).extra x)).Finite :=
  (profileAt v signed x).finite_natExtra

end IntersectionCoordinates

include hval in
/-- Multiplicativity of actual valuations turns a single raw with the prescribed
column profile into that translation at every nonzero field element. -/
theorem column_multiplier_of_values (index : (k : Bool) → J k → ℕ) (sign : (k : Bool) → J k → ℤ)
    (e : Columns J) (u : Fˣ) (hu : signed u = (signed 1).translate index sign e) (x : Fˣ) :
    signed (x*u) = (signed x).translate index sign e := by
  apply Profile.signedValues_injective
  funext i
  have hd := Profile.translate_difference (signed x) (signed 1) index sign e i
  rw [← hu, hval, hval, hval, Units.val_one, order_one, sub_zero] at hd
  rw [hval, Units.val_mul, order_mul (v i) x.ne_zero u.ne_zero]
  omega

/-- For a full valuation intersection, the singleton columns and coarse
horizontal/guard lifts suffice for the ring-level pair realization. -/
def intersectionRealizationOfColumns
    (index : (k : Bool) → J k → ℕ) (sign : (k : Bool) → J k → ℤ)
    (hmass : ∀ u, (signed u).MassEquations index sign)
    (hR : ∀ k n, ∃ u, signed u = (signed 1).addColumns index sign
      (Pi.single k (Finsupp.single n 1)) 0 0)
    (hQ : ∀ k n, ∃ u, signed u = (signed 1).addColumns index sign
      0 (Pi.single k (Finsupp.single n 1)) 0)
    (hS : ∀ k j, ∃ u, signed u = (signed 1).addColumns index sign
      0 0 (Pi.single k (Finsupp.single j 1)))
    (hbase : ∀ t : Profile J G H, t.MassEquations index sign →
      ∃ b, (signed b).height = t.height ∧ (signed b).guards = t.guards ∧
        (signed b).horizontal = t.horizontal) :
    DyadicProfiles.Realization (fullIntersection v) (Supplement J G H) := by
  apply intersectionRealization v signed hval index sign hmass
  intro t ht
  apply exists_of_calibrated_columns index sign signed hmass ?_ ?_ ?_ t ht (hbase t ht)
  · intro k n
    obtain ⟨u, hu⟩ := hR k n
    exact ⟨u, column_multiplier_of_values v signed hval index sign (_, 0, 0) u hu⟩
  · intro k n
    obtain ⟨u, hu⟩ := hQ k n
    exact ⟨u, column_multiplier_of_values v signed hval index sign (0, _, 0) u hu⟩
  · intro k j
    obtain ⟨u, hu⟩ := hS k j
    exact ⟨u, column_multiplier_of_values v signed hval index sign (0, 0, _) u hu⟩

end UnconditionalCounterexample.DyadicDeviations
