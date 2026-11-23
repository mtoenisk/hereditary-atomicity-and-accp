import UnconditionalCounterexample.Variations.DyadicLabels
import UnconditionalCounterexample.Variations.DyadicDeviations
import UnconditionalCounterexample.Variations.UnivariateSelection

/-!
# The finite signed profile before calibration

The assigned regular sites use their observed values minus the predicted
horizontal tail. Unassigned regular sites retain that tail, and unassigned
auxiliary and guard coordinates are zero. A new screened fibre leaves every
previously frozen channel sum unchanged.
-/

noncomputable section
namespace UnconditionalCounterexample.Calibration

open Polynomial DyadicDeviations DyadicColumns Variations.DyadicLedger

variable {I H : Type*}

def regularRow (r : Option FibreRole) (centre channel : Bool) (z : ℤ) : ℕ →₀ ℤ :=
  match r with
  | some (.regular c k i) => if c = centre ∧ k = channel then Finsupp.single i z else 0
  | _ => 0

def auxiliaryRow (r : Option FibreRole) (v : I) (channel : Bool) (z : ℤ) : I →₀ ℤ :=
  match r with
  | some (.auxiliary k _ _) => if k = channel then Finsupp.single v z else 0
  | _ => 0

/-- Forecast order of the frozen polynomial on a newly screened primary. -/
def forecastOrder (height : Bool → ℤ) : Option FibreRole → ℤ
  | some (.regular c _ _) => height c
  | _ => 0

/-- Deviation contributed by a fibre, including its guard with opposite weight. -/
def discrepancy (r : Option FibreRole) (height : Bool → ℤ) (k : Bool) (u v : ℤ) : ℚ :=
  r.elim 0 (fun a => a.contribution k (u - forecastOrder height r) v)

def auxWeight (role : I → Option FibreRole) (_ : Bool) (i : I) : ℕ :=
  (role i).elim 0 FibreRole.index

def auxSign (role : I → Option FibreRole) (_ : Bool) (i : I) : ℤ :=
  (role i).elim 1 FibreRole.sign

/-- One provisional profile encodes the four eventual sequences, all guards,
and both channels' finite auxiliary values. -/
def provisionalProfile (assigned : Finset I) (role : I → Option FibreRole)
    (height : Bool → ℤ) (primary guard : I → ℤ) (horizontal : H →₀ ℤ) :
    Profile (fun _ => I) I H where
  height := height
  plusDeviation k := ∑ i ∈ assigned, regularRow (role i) false k (primary i - height false)
  minusDeviation k := ∑ i ∈ assigned, regularRow (role i) true k (primary i - height true)
  auxiliary k := ∑ i ∈ assigned, auxiliaryRow (role i) i k (primary i)
  guards := {
    plus k := ∑ i ∈ assigned, regularRow (role i) false k (guard i)
    minus k := ∑ i ∈ assigned, regularRow (role i) true k (guard i)
    auxiliary k := ∑ i ∈ assigned, auxiliaryRow (role i) i k (guard i)
    lone := ∑ i ∈ assigned, if (role i).isNone then Finsupp.single i (guard i) else 0 }
  horizontal := horizontal

private theorem row_mass (role : I → Option FibreRole) (height : Bool → ℤ)
    (k : Bool) (i : I) (u v : ℤ) :
    mass (regularRow (role i) false k (u - height false)) -
        mass (regularRow (role i) true k (u - height true)) -
      (mass (regularRow (role i) false k v) - mass (regularRow (role i) true k v)) +
      (mass (auxiliaryTransfer (auxWeight role k) (auxSign role k) (auxiliaryRow (role i) i k u)) -
        mass (auxiliaryTransfer (auxWeight role k) (auxSign role k) (auxiliaryRow (role i) i k v))) =
    discrepancy (role i) height k u v := by
  have hsingle (z : ℤ) :
      mass (auxiliaryTransfer (auxWeight role k) (auxSign role k) (Finsupp.single i z)) =
        ((z * auxSign role k i : ℤ) : ℚ) * DyadicProfiles.weight (auxWeight role k i) := by
    simp [auxiliaryTransfer, mass_single, DyadicProfiles.weight, DyadicProfiles.tailWeight]
  cases h : role i with
  | none => simp [regularRow, auxiliaryRow, discrepancy]
  | some r =>
    cases r with
    | regular c t j =>
      cases c <;> by_cases ht : t = k <;>
        simp [regularRow, auxiliaryRow, ht, discrepancy, forecastOrder, FibreRole.contribution,
          FibreRole.channel, FibreRole.sign, FibreRole.index, mass_single, DyadicProfiles.weight,
          DyadicProfiles.tailWeight] <;> ring
    | auxiliary t j e =>
      cases e <;> by_cases ht : t = k <;>
        simp [regularRow, auxiliaryRow, ht, discrepancy, forecastOrder, hsingle, auxWeight, auxSign,
          h, FibreRole.contribution, FibreRole.channel, FibreRole.sign, FibreRole.index] <;> ring

/-- The current mass is the predictable regular tail plus one finite signed
discrepancy for each assigned fibre. In particular a guard-only prime does
not affect either mass, irrespective of its evaluation. -/
theorem provisional_signedMass (assigned : Finset I) (role : I → Option FibreRole)
    (height : Bool → ℤ) (primary guard : I → ℤ) (horizontal : H →₀ ℤ) (k : Bool) :
    (provisionalProfile assigned role height primary guard horizontal).signedMass
      (auxWeight role) (auxSign role) k = (height false : ℚ) - height true +
        ∑ i ∈ assigned, discrepancy (role i) height k (primary i) (guard i) := by
  have hsum := Finset.sum_congr (s₁ := assigned) rfl
    (fun i _ => row_mass role height k i (primary i) (guard i))
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib] at hsum
  simp only [Profile.signedMass, Profile.regularMass, provisionalProfile, map_sub, map_sum]
  linear_combination hsum

/-- If a later assignment agrees on old fibres and has the predicted values
at the new paired fibres, the frozen polynomial keeps its previous mass. -/
theorem provisional_signedMass_persistent {A B : Finset I} (hs : A ⊆ B)
    (role oldRole : I → Option FibreRole) (height : Bool → ℤ)
    (primary guard oldPrimary oldGuard : I → ℤ) (horizontal : H →₀ ℤ)
    (hold : ∀ i ∈ A, role i = oldRole i ∧ primary i = oldPrimary i ∧ guard i = oldGuard i)
    (hnew : ∀ i ∈ B, i ∉ A → ∀ r, role i = some r →
      primary i = forecastOrder height (some r) ∧ guard i = 0) (k : Bool) :
    (provisionalProfile B role height primary guard horizontal).signedMass
        (auxWeight role) (auxSign role) k =
      (provisionalProfile A oldRole height oldPrimary oldGuard horizontal).signedMass
        (auxWeight oldRole) (auxSign oldRole) k := by
  rw [provisional_signedMass, provisional_signedMass]
  congr 1
  calc
    _ = ∑ i ∈ A, discrepancy (role i) height k (primary i) (guard i) := by
      symm
      apply Finset.sum_subset hs
      intro i hi hi'
      cases hr : role i with
      | none => rfl
      | some r =>
        obtain ⟨hp, hg⟩ := hnew i hi hi' r hr
        simp [discrepancy, hp, hg]
    _ = _ := Finset.sum_congr rfl fun i hi => by
      obtain ⟨hr, hp, hg⟩ := hold i hi
      rw [hr, hp, hg]

/-- Integer order of the actual polynomial evaluation at a chosen finite
table entry. At a guard-only site the primary value is unused. -/
def tableOrder {A : Finset GuardSupport.PrimeIndex} (table : Variations.Univariate.Table A)
    (f : ℤ[X]) (branch : Bool) (p : GuardSupport.PrimeIndex) : ℤ :=
  if h : p ∈ A then (aeval ((table p h).branch branch) f).valuation else 0

/-- The provisional profile can be computed from the very table supplied to
the next raw selector. -/
def tableProfile {A : Finset GuardSupport.PrimeIndex} (table : Variations.Univariate.Table A)
    (role : GuardSupport.PrimeIndex → Option FibreRole) (f : ℤ[X]) (height : Bool → ℤ)
    (horizontal : H →₀ ℤ) :=
  provisionalProfile A role height (tableOrder table f false) (tableOrder table f true) horizontal

end UnconditionalCounterexample.Calibration
