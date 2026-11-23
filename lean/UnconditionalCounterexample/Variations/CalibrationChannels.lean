import UnconditionalCounterexample.Variations.CalibrationSchedule
import UnconditionalCounterexample.Variations.CalibrationProfiles
import UnconditionalCounterexample.Variations.FrozenSites

/-! # Simultaneous corrections of the two channel masses -/

noncomputable section
namespace UnconditionalCounterexample.Calibration

open Polynomial GuardSupport RecursivePrefix Variations.Univariate

variable {n : ℕ} {P : Prefix n} {f G : ℤ[X]}

/-- One signed auxiliary weight and its actual realization at a fresh prime. -/
structure Correction {n : ℕ} (P : Prefix n) (f G : ℤ[X]) where
  index : ℕ
  order : ℕ
  site : AtPrefix P f G order
  sign : ℤ
  sign_eq : sign = 1 ∨ sign = -1

def Correction.mass (c : Correction P f G) : ℚ :=
  c.sign * (((aeval c.site.primary.val.val f).valuation -
    (aeval c.site.guard.value.val f).valuation : ℤ) : ℚ) * DyadicProfiles.weight c.index

def correctionBirths : Option (Correction P f G) → Births P
  | some c => c.site.births
  | none => {
    primes := ∅
    fresh p hp := (Finset.notMem_empty p hp).elim
    guard p hp := (Finset.notMem_empty p hp).elim
    birth_eq p hp := (Finset.notMem_empty p hp).elim
    old_units p hp := (Finset.notMem_empty p hp).elim
    primary p hp := (Finset.notMem_empty p hp).elim }

def correctionMass : Option (Correction P f G) → ℚ
  | some c => c.mass
  | none => 0

/-- The same weighted contribution obtained by extending the signed profile
with the actual primary order and zero guard value at the new site. -/
theorem corrected_profile_mass {J : Bool → Type*} {Gd H : Type*}
    (p : DyadicDeviations.Profile J Gd H) (index : (k : Bool) → J k → ℕ)
    (sign : (k : Bool) → J k → ℤ) (c : Bool → Option (Correction P f G)) (k : Bool) :
    (extendProfile p (fun b => (c b).elim 0 (fun u => (u.order : ℤ)))).signedMass
      (fun b j => j.elim ((c b).elim 0 Correction.index) (index b))
      (fun b j => j.elim ((c b).elim 1 Correction.sign) (sign b)) k =
      p.signedMass index sign k + correctionMass (c k) := by
  rw [signedMass_extendProfile]
  cases hc : c k with
  | none => simp [correctionMass]
  | some u => simp [correctionMass, Correction.mass, u.site.toAuxiliarySite.paired_order.1, mul_comm]

/-- Both channels are corrected on one prefix and their disjoint fibres
form one admissible batch. A channel already at its target uses no prime. -/
theorem exists_two_channel_correction (P : Prefix n) (f G : ℤ[X]) (hd : f.natDegree ≠ 0)
    (hprim : f.IsPrimitive) (hirr : Irreducible f) (hG : G ≠ 0)
    (hc : IsCoprime (f.map (algebraMap ℤ ℚ)) (G.map (algebraMap ℤ ℚ)))
    (hraw : ∀ j : Fin n, IsCoprime (f.map (algebraMap ℤ ℚ)) (P.raw j))
    {J : Bool → Type*} {Gd H : Type*} (profile : DyadicDeviations.Profile J Gd H)
    (index : (k : Bool) → J k → ℕ) (sign : (k : Bool) → J k → ℤ)
    (target : Bool → ℤ) (cutoff L : ℕ) :
    ∃ (c : Bool → Option (Correction P f G)) (batch : Births P),
      (∀ k, c k = none ↔ profile.signedMass index sign k = target k) ∧
      (∀ k, profile.signedMass index sign k + correctionMass (c k) = target k) ∧
      (∀ k u, c k = some u → L ≤ u.index ∧ cutoff < u.site.prime.val) ∧
      Disjoint (correctionBirths (c false)).primes (correctionBirths (c true)).primes ∧
      batch.primes = (correctionBirths (c false)).primes ∪ (correctionBirths (c true)).primes ∧
      ∀ k p (hp : p ∈ (correctionBirths (c k)).primes), ∃ h : p ∈ batch.primes,
        batch.site p h = (correctionBirths (c k)).site p hp := by
  classical
  let M := profile.signedMass index sign
  have one (k : Bool) (bound : ℕ) :
      ∃ c : Option (Correction P f G), (c = none ↔ M k = target k) ∧
        M k + correctionMass c = target k ∧
        ∀ u, c = some u → L ≤ u.index ∧ bound < u.site.prime.val := by
    by_cases h : M k = target k
    · exact ⟨none, by simp [h], by simpa [correctionMass] using h, by simp⟩
    · have hdiff : (target k : ℚ) - M k ≠ 0 := sub_ne_zero.mpr (Ne.symm h)
      obtain ⟨i, hi, l, s, hs, ε, hε, hm⟩ := exists_correction P f G hd hprim hirr hG hc
        hraw profile index sign k (target k) bound L hdiff
      let c : Correction P f G := ⟨i, l, s, ε, hε⟩
      refine ⟨some c, by simp [h], ?_, ?_⟩
      · simpa only [correctionMass, Correction.mass, c, order_zero_of_unit _ _ s.guard_unit,
          sub_zero] using hm
      · rintro u hu
        exact Option.some.inj hu ▸ And.intro hi hs
  obtain ⟨a, ha, hma, hia⟩ := one false cutoff
  let A := correctionBirths a
  let limit := max cutoff (A.primes.sup Subtype.val)
  obtain ⟨b, hb, hmb, hib⟩ := one true limit
  let B := correctionBirths b
  have hdis : Disjoint A.primes B.primes := by
    apply Finset.disjoint_left.mpr
    intro p hpA hpB
    cases h : b with
    | none => simp [B, h, correctionBirths] at hpB
    | some u =>
      have he : p = u.site.prime := by
        apply Finset.mem_singleton.mp
        simpa only [B, h, correctionBirths, AtPrefix.births, Births.singleton] using hpB
      have hl := (hib u h).2
      exact (not_le_of_gt hl) (he ▸ (Finset.le_sup (f := Subtype.val) hpA).trans
        (le_max_right cutoff _))
  let c : Bool → Option (Correction P f G) := fun k => if k then b else a
  refine ⟨c, A.union B hdis, ?_, ?_, ?_, hdis, rfl, ?_⟩
  · intro k; cases k <;> first | exact ha | exact hb
  · intro k; cases k <;> first | exact hma | exact hmb
  · intro k u hu
    cases k with
    | false => exact hia u hu
    | true =>
      have h := hib u hu
      exact ⟨h.1, (le_max_left ..).trans_lt h.2⟩
  · intro k p hp
    cases k with
    | false => exact ⟨Finset.mem_union_left _ hp, A.union_site_left B hdis p hp⟩
    | true => exact ⟨Finset.mem_union_right _ hp, A.union_site_right B hdis p hp⟩

end UnconditionalCounterexample.Calibration
