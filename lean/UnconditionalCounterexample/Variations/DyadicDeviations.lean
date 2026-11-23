import UnconditionalCounterexample.Variations.DyadicColumns
import UnconditionalCounterexample.Variations.DyadicProfiles

/-!
# Signed profiles with two horizontal centres

The four regular sequences are stored as their two horizontal limit values plus
finite integer deviations. Each paired guard has the opposite weight from its
primary. A lone guard and a retained noncentral horizontal have zero weight.
-/

noncomputable section

namespace UnconditionalCounterexample.DyadicDeviations

open DyadicColumns (auxiliaryTransfer adjacent)

variable {J : Bool → Type*} {G H : Type*}

/-- Guard values, indexed by their paired primary, together with the lone guards. -/
structure Guards (J : Bool → Type*) (G : Type*) where
  plus : Bool → ℕ →₀ ℤ
  minus : Bool → ℕ →₀ ℤ
  auxiliary : (k : Bool) → J k →₀ ℤ
  lone : G →₀ ℤ

/-- The two channels of a signed profile. Each finite auxiliary site belongs
to exactly one channel. Retained horizontal primes other than the two centres
are indexed by `H`. -/
@[ext] structure Profile (J : Bool → Type*) (G H : Type*) where
  height : Bool → ℤ
  plusDeviation : Bool → ℕ →₀ ℤ
  minusDeviation : Bool → ℕ →₀ ℤ
  auxiliary : (k : Bool) → J k →₀ ℤ
  guards : Guards J G
  horizontal : H →₀ ℤ

namespace Profile

def plus (p : Profile J G H) (k : Bool) (n : ℕ) : ℤ :=
  p.height false + p.plusDeviation k n

def minus (p : Profile J G H) (k : Bool) (n : ℕ) : ℤ :=
  p.height true + p.minusDeviation k n

/-- The constant difference contributes its entire value, since the regular
weights sum to one. -/
def regularMass (p : Profile J G H) (k : Bool) : ℚ :=
  (p.height false : ℚ) - p.height true +
    DyadicColumns.mass (p.plusDeviation k - p.minusDeviation k)

/-- Add auxiliary contributions and subtract the mass at each paired guard. -/
def signedMass (p : Profile J G H) (index : (k : Bool) → J k → ℕ)
    (sign : (k : Bool) → J k → ℤ) (k : Bool) : ℚ :=
  p.regularMass k - DyadicColumns.mass (p.guards.plus k - p.guards.minus k) +
    DyadicColumns.mass (auxiliaryTransfer (index k) (sign k)
      (p.auxiliary k - p.guards.auxiliary k))

/-- The two linear relations on a principal profile of the dyadic construction. -/
def MassEquations (p : Profile J G H) (index : (k : Bool) → J k → ℕ)
    (sign : (k : Bool) → J k → ℤ) : Prop :=
  ∀ k, p.signedMass index sign k = (p.height k : ℚ)

private theorem constant_mass (N : ℕ) (c : ℚ) : DyadicProfiles.mass N (fun _ => c) c = c := by
  induction N with
  | zero => rfl
  | succ N ih => change (c + DyadicProfiles.mass N (fun _ => c) c) / 2 = c; rw [ih]; ring

/-- Adding finitely many deviations to a constant tail gives exactly the
finite weighted mass of those deviations plus the constant. -/
theorem cutoff_mass (d : ℕ →₀ ℤ) (c : ℤ) (N : ℕ) (hs : d.support ⊆ Finset.range N) :
    DyadicProfiles.mass N (fun n => ((c + d n : ℤ) : ℚ)) c = c + DyadicColumns.mass d := by
  have hc := constant_mass N (c : ℚ)
  have hd : DyadicColumns.mass d =
      ∑ i ∈ Finset.range N, DyadicProfiles.weight i * (d i : ℚ) := by
    change d.sum (fun i z => z • ((1 / 2 : ℚ) ^ (i+1))) = _
    rw [Finsupp.sum_of_support_subset _ hs _ (by simp)]
    simp only [zsmul_eq_mul, DyadicProfiles.weight, DyadicProfiles.tailWeight, mul_comm]
  rw [DyadicProfiles.mass_eq_sum] at hc ⊢
  simp_rw [Int.cast_add, mul_add]
  rw [Finset.sum_add_distrib, hd]
  linarith

/-- The finite-deviation and cutoff descriptions of regular signed mass agree. -/
theorem regularMass_eq_cutoff (p : Profile J G H) (k : Bool) (N : ℕ)
    (hs : (p.plusDeviation k - p.minusDeviation k).support ⊆ Finset.range N) :
    p.regularMass k = DyadicProfiles.mass N (fun n => (p.plus k n : ℚ) - p.minus k n)
      ((p.height false : ℚ) - p.height true) := by
  have h := cutoff_mass (p.plusDeviation k - p.minusDeviation k)
    (p.height false - p.height true) N hs
  simp only [Int.cast_add, Int.cast_sub, Finsupp.sub_apply] at h
  rw [regularMass, ← h]
  congr 1
  funext n
  simp only [plus, minus, Int.cast_add]
  ring

/-- Add a finite integral combination of the balanced columns R, the adjacent
columns Q, and the auxiliary corrections S, independently on each channel. -/
def addColumns (p : Profile J G H) (index : (k : Bool) → J k → ℕ)
    (sign : (k : Bool) → J k → ℤ) (r q : Bool → ℕ →₀ ℤ) (s : (k : Bool) → J k →₀ ℤ) :
    Profile J G H :=
  { p with
    plusDeviation := fun k =>
      p.plusDeviation k + r k + adjacent (q k) - auxiliaryTransfer (index k) (sign k) (s k)
    minusDeviation := fun k => p.minusDeviation k + r k
    auxiliary := fun k => p.auxiliary k + s k }

theorem signedMass_addColumns (p : Profile J G H) (index : (k : Bool) → J k → ℕ)
    (sign : (k : Bool) → J k → ℤ) (r q : Bool → ℕ →₀ ℤ) (s : (k : Bool) → J k →₀ ℤ)
    (k : Bool) : (p.addColumns index sign r q s).signedMass index sign k =
      p.signedMass index sign k := by
  simp only [signedMass, regularMass, addColumns, map_add, map_sub, DyadicColumns.mass_adjacent]
  ring

/-- Profiles satisfying the principal mass equations and agreeing on all
horizontal and guard coordinates differ by integral R, Q and S columns.
The R and S exponents are the actual differences at the minus and auxiliary sites. -/
theorem exists_columns_of_massEquations (p t : Profile J G H)
    (index : (k : Bool) → J k → ℕ) (sign : (k : Bool) → J k → ℤ)
    (hp : p.MassEquations index sign) (ht : t.MassEquations index sign)
    (hh : p.height = t.height) (hg : p.guards = t.guards) (hhoriz : p.horizontal = t.horizontal) :
    ∃ q : Bool → ℕ →₀ ℤ, p.addColumns index sign
      (fun k => t.minusDeviation k - p.minusDeviation k) q
      (fun k => t.auxiliary k - p.auxiliary k) = t := by
  have hq (k : Bool) : ∃ q : ℕ →₀ ℤ,
      adjacent q = (t.plusDeviation k - p.plusDeviation k) -
        (t.minusDeviation k - p.minusDeviation k) +
        auxiliaryTransfer (index k) (sign k) (t.auxiliary k - p.auxiliary k) := by
    refine ((DyadicColumns.mass_eq_zero_iff_existsUnique_adjacent _).mp ?_).exists
    have he := (hp k).trans ((congrArg (fun f : Bool → ℤ => (f k : ℚ)) hh).trans (ht k).symm)
    simp only [signedMass, regularMass, map_add, map_sub, hh, hg] at he ⊢
    linarith
  choose q h using hq
  refine ⟨q, Profile.ext hh ?_ ?_ ?_ hg hhoriz⟩
  · funext k
    change p.plusDeviation k + (t.minusDeviation k - p.minusDeviation k) + adjacent (q k) -
      auxiliaryTransfer (index k) (sign k) (t.auxiliary k - p.auxiliary k) = t.plusDeviation k
    rw [h k]
    abel
  · funext k
    change p.minusDeviation k + (t.minusDeviation k - p.minusDeviation k) = _
    abel
  · funext k
    change p.auxiliary k + (t.auxiliary k - p.auxiliary k) = _
    abel

/-- A nonzero error at a frozen polynomial can be corrected by one auxiliary
site of arbitrarily fine weight with one sign and a positive integral order. -/
theorem exists_calibration (p : Profile J G H) (index : (k : Bool) → J k → ℕ)
    (sign : (k : Bool) → J k → ℤ) (k : Bool) (target : ℤ) (L : ℕ)
    (hne : (target : ℚ) - p.signedMass index sign k ≠ 0) :
    ∃ n ≥ L, ∃ l : ℕ, 0 < l ∧
      ((target : ℚ) - p.signedMass index sign k = (l : ℚ) * DyadicProfiles.weight n ∨
       (target : ℚ) - p.signedMass index sign k = -(l : ℚ) * DyadicProfiles.weight n) := by
  let c := target - p.height false + p.height true
  let d := Finsupp.single 0 (2*c) - (p.plusDeviation k - p.minusDeviation k) +
    (p.guards.plus k - p.guards.minus k) -
    auxiliaryTransfer (index k) (sign k) (p.auxiliary k - p.guards.auxiliary k)
  have hc : DyadicColumns.mass (Finsupp.single 0 (2*c)) = (c : ℚ) := by
    rw [DyadicColumns.mass_single]
    push_cast
    ring
  have hd : DyadicColumns.mass d = (target : ℚ) - p.signedMass index sign k := by
    simp only [d, map_add, map_sub, hc, c, signedMass, regularMass, Int.cast_add, Int.cast_sub]
    ring
  obtain ⟨n, hn, z, hz⟩ := DyadicColumns.mass_eq_multiple_of_late_weight d L
  rw [hd] at hz
  have hz0 : z ≠ 0 := by
    intro h0
    exact hne (by simpa [h0] using hz)
  cases z with
  | ofNat l =>
    refine ⟨n, hn, l, ?_, Or.inl ?_⟩
    · exact Nat.pos_of_ne_zero (fun he => hz0 (by simp [he]))
    · simpa [DyadicProfiles.weight, DyadicProfiles.tailWeight] using hz
  | negSucc l =>
    refine ⟨n, hn, l+1, by omega, Or.inr ?_⟩
    simpa [DyadicProfiles.weight, DyadicProfiles.tailWeight] using hz

private def deviation (f : ℕ → ℕ) (c N : ℕ) (hs : ∀ n ≥ N, f n = c) : ℕ →₀ ℤ :=
  Finsupp.onFinset (Finset.range N) (fun n => (f n : ℤ) - c) (by
    intro n hn
    apply Finset.mem_range.mpr
    by_contra h
    exact hn (by rw [hs n (by omega), sub_self]))

/-- Include an effective regular profile by giving every supplementary site
value zero. This also embeds the two explicit witnesses into the signed model. -/
def ofRegular (p : DyadicProfiles.Profile) : Profile J G H where
  height k := p.height k
  plusDeviation k := deviation (p.plus k) (p.height false) p.cutoff (p.plus_stable k)
  minusDeviation k := deviation (p.minus k) (p.height true) p.cutoff (p.minus_stable k)
  auxiliary _ := 0
  guards := ⟨fun _ => 0, fun _ => 0, fun _ => 0, 0⟩
  horizontal := 0

theorem signedMass_ofRegular (p : DyadicProfiles.Profile)
    (index : (k : Bool) → J k → ℕ) (sign : (k : Bool) → J k → ℤ) (k : Bool) :
    (ofRegular p : Profile J G H).signedMass index sign k = p.signedMass k := by
  let t : Profile J G H := ofRegular p
  have hs : (t.plusDeviation k - t.minusDeviation k).support ⊆ Finset.range p.cutoff := by
    intro n hn
    by_contra h
    have he : p.cutoff ≤ n := Nat.le_of_not_gt (mt Finset.mem_range.mpr h)
    apply Finsupp.mem_support_iff.mp hn
    simp [t, ofRegular, deviation, p.plus_stable k n he, p.minus_stable k n he]
  change t.signedMass index sign k = _
  rw [signedMass, t.regularMass_eq_cutoff k p.cutoff hs]
  simp [t, ofRegular, deviation, plus, minus, DyadicProfiles.Profile.signedMass,
    DyadicProfiles.Profile.tailDifference]
  rfl

end Profile
end UnconditionalCounterexample.DyadicDeviations
