import UnconditionalCounterexample.Variations.DyadicIntersections
import UnconditionalCounterexample.Variations.SplitProfiles

/-!
# The full signed profile split

The regular binary corrections are combined with an assignment of whole
supplementary fibres. Every auxiliary and its guard are placed in the same
factor. The factor with zero height at one retains all lone guards and all
noncentral horizontal valuations.
-/

namespace UnconditionalCounterexample.DyadicDeviations

variable {J : Bool → Type*} {G H : Type*}

/-- Channel assignment for a supplementary coordinate. Lone guards and the
noncentral horizontals go to the first factor. -/
def Supplement.channel : Supplement J G H → Bool
  | .auxiliary k _ | .plusGuard k _ | .minusGuard k _ | .auxiliaryGuard k _ => k
  | .loneGuard _ | .horizontal _ => false

namespace Profile

/-- Impose effective regular values and keep exactly the supplementary
coordinates assigned to the indicated factor. -/
noncomputable def assign (p : Profile J G H) (a : DyadicProfiles.Profile) (c : Bool) :
    Profile J G H :=
  { (ofRegular a : Profile J G H) with
    auxiliary := fun k => if k = c then p.auxiliary k else 0
    guards := {
      plus := fun k => if k = c then p.guards.plus k else 0
      minus := fun k => if k = c then p.guards.minus k else 0
      auxiliary := fun k => if k = c then p.guards.auxiliary k else 0
      lone := if c then 0 else p.guards.lone }
    horizontal := if c then 0 else p.horizontal }

@[simp] theorem assign_height (p : Profile J G H) (a : DyadicProfiles.Profile) (c k : Bool) :
    (p.assign a c).height k = (a.height k : ℤ) := rfl

@[simp] theorem assign_plus (p : Profile J G H) (a : DyadicProfiles.Profile) (c k : Bool) (n : ℕ) :
    (p.assign a c).plus k n = (a.plus k n : ℤ) := by
  change (a.height false : ℤ) + ((a.plus k n : ℤ) - a.height false) = _
  omega

@[simp] theorem assign_minus (p : Profile J G H) (a : DyadicProfiles.Profile) (c k : Bool) (n : ℕ) :
    (p.assign a c).minus k n = (a.minus k n : ℤ) := by
  change (a.height true : ℤ) + ((a.minus k n : ℤ) - a.height true) = _
  omega

theorem assign_supplement (p : Profile J G H) (a : DyadicProfiles.Profile) (c : Bool)
    (i : Supplement J G H) : (p.assign a c).signedValues (.other i) =
      if i.channel = c then p.signedValues (.other i) else 0 := by
  cases i with
  | auxiliary k j | plusGuard k j | minusGuard k j | auxiliaryGuard k j =>
    cases k <;> cases c <;> rfl
  | loneGuard _ | horizontal _ => cases c <;> rfl

private theorem regularMass_ofRegular (a : DyadicProfiles.Profile)
    (index : (k : Bool) → J k → ℕ) (sign : (k : Bool) → J k → ℤ) (k : Bool) :
    (ofRegular a : Profile J G H).regularMass k = a.signedMass k := by
  simpa [signedMass, ofRegular] using
    (signedMass_ofRegular (G := G) (H := H) a index sign k)

theorem regularMass_natRegular (p : Profile J G H)
    (index : (k : Bool) → J k → ℕ) (sign : (k : Bool) → J k → ℤ)
    (hn : ∀ i, 0 ≤ p.signedValues i) (k : Bool) :
    p.regularMass k = p.natRegular.signedMass k := by
  have hh (j : Bool) : (p.natRegular.height j : ℤ) = p.height j :=
    Int.toNat_of_nonneg (hn (.centre j))
  have heplus : (ofRegular p.natRegular : Profile J G H).plusDeviation k = p.plusDeviation k := by
    ext n
    change ((p.plus k n).toNat : ℤ) - p.natRegular.height false = _
    rw [Int.toNat_of_nonneg (show 0 ≤ p.plus k n from hn (.plus k n)), hh]
    simp [plus]
  have heminus : (ofRegular p.natRegular : Profile J G H).minusDeviation k = p.minusDeviation k := by
    ext n
    change ((p.minus k n).toNat : ℤ) - p.natRegular.height true = _
    rw [Int.toNat_of_nonneg (show 0 ≤ p.minus k n from hn (.minus k n)), hh]
    simp [minus]
  rw [← regularMass_ofRegular (G := G) (H := H) p.natRegular index sign k]
  unfold regularMass
  rw [heplus, heminus]
  change _ = ((p.natRegular.height false : ℤ) : ℚ) - ((p.natRegular.height true : ℤ) : ℚ) + _
  rw [hh, hh]

/-- The entire nonregular contribution in the chosen channel survives with its
original sign, including the opposite weight of every paired guard. -/
theorem signedMass_assign (p : Profile J G H) (a : DyadicProfiles.Profile) (c k : Bool)
    (index : (k : Bool) → J k → ℕ) (sign : (k : Bool) → J k → ℤ) :
    (p.assign a c).signedMass index sign k = a.signedMass k +
      if k = c then p.signedMass index sign k - p.regularMass k else 0 := by
  have hr : (p.assign a c).regularMass k = a.signedMass k :=
    regularMass_ofRegular (G := G) (H := H) a index sign k
  simp only [signedMass, hr]
  by_cases h : k = c <;> simp [assign, h]
  ring

end Profile

variable (index : (k : Bool) → J k → ℕ) (sign : (k : Bool) → J k → ℤ)

/-- The data used by the split task at reserved channel-one index `M`. -/
structure SplitAt (p u v : Profile J G H) (M : ℕ) : Prop where
  effective : ∀ i, 0 ≤ u.signedValues i ∧ 0 ≤ v.signedValues i
  values_sum : ∀ i, u.signedValues i + v.signedValues i = p.signedValues i
  masses_left : u.MassEquations index sign
  masses_right : v.MassEquations index sign
  heights : u.height false = p.height false ∧ u.height true = 0 ∧
    v.height false = 0 ∧ v.height true = p.height true
  old_regular : ∀ i < M, u.plus false i = p.plus false i ∧ u.minus false i = p.minus false i ∧
    u.plus true i = 0 ∧ u.minus true i = 0
  supplementary : ∀ i, u.signedValues (.other i) =
    if i.channel = false then p.signedValues (.other i) else 0
  reserved : u.plus true M = 1 ∧ u.minus true M = 1

/-- The two points of an already-classified fibre have one assignment. Its
regular primary is earlier than the reserved index; its paired guard or an
auxiliary/lone point is governed by the same channel. -/
inductive OldFibre (M : ℕ) (k : Bool) : DyadicProfiles.Site (Supplement J G H) → Prop where
  | plus {n : ℕ} (h : n < M) : OldFibre M k (.plus k n)
  | minus {n : ℕ} (h : n < M) : OldFibre M k (.minus k n)
  | supplementary (i : Supplement J G H) (h : i.channel = k) : OldFibre M k (.other i)

theorem SplitAt.old_fibre {p u v : Profile J G H} {M : ℕ} (split : SplitAt index sign p u v M)
    {k : Bool} {i : DyadicProfiles.Site (Supplement J G H)} (hi : OldFibre M k i) :
    u.signedValues i = if k = false then p.signedValues i else 0 := by
  cases hi with
  | plus h =>
    cases k
    · exact (split.old_regular _ h).1
    · exact (split.old_regular _ h).2.2.1
  | minus h =>
    cases k
    · exact (split.old_regular _ h).2.1
    · exact (split.old_regular _ h).2.2.2
  | supplementary j hj => simpa [hj] using split.supplementary j

/-- Split any effective signed principal profile. All of its coordinates are
partitioned and both resulting full profiles satisfy the two principal equations. -/
theorem exists_split_signed (p : Profile J G H) (hp : p.MassEquations index sign)
    (hn : ∀ i, 0 ≤ p.signedValues i) (hr : 0 < p.height false) (hs : 0 < p.height true)
    (M : ℕ) (hM : p.natRegular.cutoff ≤ M) :
    ∃ u v, SplitAt index sign p u v M := by
  have hh (k : Bool) : (p.natRegular.height k : ℤ) = p.height k :=
    Int.toNat_of_nonneg (hn (.centre k))
  have hplus (k n) : (p.natRegular.plus k n : ℤ) = p.plus k n :=
    Int.toNat_of_nonneg (hn (.plus k n))
  have hminus (k n) : (p.natRegular.minus k n : ℤ) = p.minus k n :=
    Int.toNat_of_nonneg (hn (.minus k n))
  obtain ⟨a, b, _, ha0, ha1, hb0, hb1, hsum, hma0, hma1, hmb0, hmb1, hold, hreserve⟩ :=
    DyadicSplit.exists_split_profiles p.natRegular M hM
      (by exact_mod_cast (hh false).symm ▸ hr) (by exact_mod_cast (hh true).symm ▸ hs)
  have htotal (k : Bool) : p.signedMass index sign k = (p.natRegular.height k : ℚ) := by
    rw [hp k, ← hh]
    norm_cast
  let u := p.assign a false
  let v := p.assign b true
  refine ⟨u, v, ?_, ?_, ?_, ?_, ?_, ?_, p.assign_supplement a false, ?_⟩
  · intro i
    cases i with
    | centre k => exact ⟨Int.natCast_nonneg _, Int.natCast_nonneg _⟩
    | plus k n | minus k n =>
      simp [u, v, Profile.signedValues]
    | other i =>
      dsimp only [u, v]
      rw [Profile.assign_supplement,
        Profile.assign_supplement]
      cases i.channel <;> simp [hn]
  · intro i
    cases i with
    | centre k =>
      cases k <;> simp [u, v, Profile.signedValues, ha0, ha1, hb0, hb1, hh]
    | plus k n =>
      change u.plus k n + v.plus k n = _
      dsimp only [u, v]
      rw [Profile.assign_plus, Profile.assign_plus,
        ← Int.natCast_add, (hsum k n).1]
      exact hplus k n
    | minus k n =>
      change u.minus k n + v.minus k n = _
      dsimp only [u, v]
      rw [Profile.assign_minus, Profile.assign_minus,
        ← Int.natCast_add, (hsum k n).2]
      exact hminus k n
    | other i =>
      change (p.assign a false).signedValues _ + (p.assign b true).signedValues _ = _
      rw [Profile.assign_supplement, Profile.assign_supplement]
      cases i.channel <;> simp
  · intro k
    change (p.assign a false).signedMass index sign k = _
    rw [Profile.signedMass_assign]
    cases k <;> simp [u, hma0, hma1, htotal, ha0, ha1, p.regularMass_natRegular index sign hn]
  · intro k
    change (p.assign b true).signedMass index sign k = _
    rw [Profile.signedMass_assign]
    cases k <;> simp [v, hmb0, hmb1, htotal, hb0, hb1, p.regularMass_natRegular index sign hn]
  · simp [u, v, ha0, ha1, hb0, hb1, hh]
  · intro n hnM
    obtain ⟨h₁, h₂, h₃, h₄⟩ := hold n hnM
    simp [u, h₁, h₂, h₃, h₄, hplus, hminus]
  · simp [u, hreserve]

/-- In the elimination relative to a base lift of the guards and horizontals,
the balanced coefficient at the reserved site equals one if the base lift
vanishes at that minus site. Neither adjacent nor auxiliary corrections affect it. -/
theorem SplitAt.reserved_coefficient {p u v : Profile J G H} {M : ℕ}
    (split : SplitAt index sign p u v M) (base : Profile J G H)
    (hbase : base.MassEquations index sign)
    (hh : base.height = u.height) (hg : base.guards = u.guards)
    (hhoriz : base.horizontal = u.horizontal) (hsite : base.minus true M = 0) :
    (u.minusDeviation true - base.minusDeviation true) M = 1 ∧
      ∃ q, base.addColumns index sign (fun k => u.minusDeviation k - base.minusDeviation k) q
        (fun k => u.auxiliary k - base.auxiliary k) = u := by
  refine ⟨?_, base.exists_columns_of_massEquations u index sign hbase split.masses_left hh hg hhoriz⟩
  have hres := split.reserved.2
  have he := congrFun hh true
  simp only [Profile.minus] at hres hsite
  change u.minusDeviation true M - base.minusDeviation true M = 1
  omega

/-- Once a field factor has the prescribed left profile, the field quotient
has the prescribed right profile, and both actually belong to the valuation
intersection. -/
theorem SplitAt.field_factors {F : Type*} [Field F] {p u v : Profile J G H} {M : ℕ}
    (split : SplitAt index sign p u v M)
    (val : DyadicProfiles.Site (Supplement J G H) → Valuation F (WithZero (Multiplicative ℤ)))
    (signed : Fˣ → Profile J G H)
    (hval : ∀ (y : Fˣ) i, (signed y).signedValues i = DiscreteOrders.order (val i) (y : F))
    (x a : Fˣ) (hx : signed x = p) (ha : signed a = u) :
    signed (x/a) = v ∧ (a : F) ∈ DiscreteOrders.fullIntersection val ∧
      ((x/a : Fˣ) : F) ∈ DiscreteOrders.fullIntersection val := by
  have hv : signed (x/a) = v := by
    apply Profile.signedValues_injective
    funext i
    have ht := split.values_sum i
    rw [← ha, ← hx, hval, hval] at ht
    rw [hval, Units.val_div_eq_div_val, DiscreteOrders.order_div _ x.ne_zero a.ne_zero]
    omega
  have mem (y : Fˣ) (he : ∀ i, 0 ≤ (signed y).signedValues i) :
      (y : F) ∈ DiscreteOrders.fullIntersection val := by
    apply (IntersectionDomain.mem_intersection ⊤ val _).mpr
    exact ⟨Subring.mem_top _, fun i => (DiscreteOrders.order_nonneg_iff _ y.ne_zero).mp
      ((hval y i) ▸ he i)⟩
  exact ⟨hv, mem a (fun i => ha ▸ (split.effective i).1),
    mem (x/a) (fun i => hv ▸ (split.effective i).2)⟩

end UnconditionalCounterexample.DyadicDeviations
