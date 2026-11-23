import UnconditionalCounterexample.Variations.CalibrationChannels
import UnconditionalCounterexample.Variations.CalibrationForecast

/-! # The mass change in the actual enlarged table of evaluation sites -/

noncomputable section
namespace UnconditionalCounterexample.Calibration

open Polynomial GuardSupport RecursivePrefix Variations.Univariate Variations.DyadicLedger

variable {n : ℕ} {P : Prefix n} {f G : ℤ[X]} {H : Type*}

def Correction.role (c : Correction P f G) (k : Bool) : FibreRole :=
  .auxiliary k c.index (decide (c.sign = 1))

private theorem Correction.energy (c : Correction P f G) (height : Bool → ℤ) (b k : Bool) :
    discrepancy (some (c.role b)) height k
      (aeval c.site.primary.val.val f).valuation (aeval c.site.guard.value.val f).valuation =
      if b = k then c.mass else 0 := by
  rcases c.sign_eq with he | he <;> by_cases hb : b = k <;>
    simp [Correction.role, discrepancy, forecastOrder, Correction.mass, FibreRole.contribution,
      FibreRole.index, FibreRole.sign, FibreRole.channel, he, hb] <;> ring

/-- Appending both selected corrections to an actual table gives the same
mass increment computed before the prime batch was processed. Any additional
new paired primes must screen this polynomial. A new guard-only prime may
take an arbitrary value. -/
theorem tableProfile_after_corrections {B : Finset PrimeIndex} (T : Table P.state.assignment.primes)
    (T' : Table B) (hAB : P.state.assignment.primes ⊆ B)
    (role role' : PrimeIndex → Option FibreRole) (height : Bool → ℤ) (hor : H →₀ ℤ)
    (c : Bool → Option (Correction P f G))
    (hold : ∀ p (hp : p ∈ P.state.assignment.primes),
      T' p (hAB hp) = T p hp ∧ role' p = role p)
    (hcal : ∀ b u, c b = some u → ∃ h : u.site.prime ∈ B,
      role' u.site.prime = some (u.role b) ∧
      T' u.site.prime h = ⟨u.site.guard.value, u.site.guard.transcendental, some u.site.primary⟩)
    (hnew : ∀ p ∈ B, p ∉ P.state.assignment.primes →
      (∃ b u, c b = some u ∧ p = u.site.prime) ∨
      (∀ r, role' p = some r → tableOrder T' f false p = forecastOrder height (some r) ∧
        tableOrder T' f true p = 0)) (k : Bool) :
    (tableProfile T' role' f height hor).signedMass (auxWeight role') (auxSign role') k =
      (tableProfile T role f height hor).signedMass (auxWeight role) (auxSign role) k +
        correctionMass (c k) := by
  classical
  let A := P.state.assignment.primes
  let D (p : PrimeIndex) := discrepancy (role' p) height k
    (tableOrder T' f false p) (tableOrder T' f true p)
  have value (b : Bool) (u : Correction P f G) (h : c b = some u) :
      D u.site.prime = if b = k then u.mass else 0 := by
    obtain ⟨hp, hr, hs⟩ := hcal b u h
    dsimp only [D]
    rw [hr]
    unfold tableOrder
    rw [dite_eq_left hp, dite_eq_left hp, hs]
    exact u.energy height b k
  have hzero (p : PrimeIndex) (hp : p ∈ B \ A)
      (ha : ∀ u, c k = some u → p ≠ u.site.prime) : D p = 0 := by
    obtain ⟨hpB, hpA⟩ := Finset.mem_sdiff.mp hp
    rcases hnew p hpB hpA with ⟨b, u, hu, rfl⟩ | hscreen
    · have hbk : b ≠ k := fun h => ha u (h ▸ hu) rfl
      simpa [hbk] using value b u hu
    · cases h : role' p with
      | none => simp [D, discrepancy, h]
      | some r =>
        obtain ⟨hv, hg⟩ := hscreen r h
        simp [D, discrepancy, h, hv, hg]
  have hmass : ∑ p ∈ B \ A, D p = correctionMass (c k) := by
    cases hc : c k with
    | none => exact Finset.sum_eq_zero (fun p hp => hzero p hp (by simp [hc]))
    | some u =>
      obtain ⟨hp, _, _⟩ := hcal k u hc
      have hh : u.site.prime ∈ B \ A := Finset.mem_sdiff.mpr ⟨hp, u.site.fresh⟩
      rw [Finset.sum_eq_single_of_mem u.site.prime hh]
      · simpa [correctionMass] using value k u hc
      · intro p hmem hpne
        apply hzero p hmem
        rintro t ht
        obtain rfl := Option.some.inj (hc.symm.trans ht)
        exact hpne
  have holdsum : ∑ p ∈ A, D p = ∑ p ∈ A, discrepancy (role p) height k
      (tableOrder T f false p) (tableOrder T f true p) := by
    apply Finset.sum_congr rfl
    intro p hp
    change p ∈ P.state.assignment.primes at hp
    obtain ⟨hs, hr⟩ := hold p hp
    simp [D, tableOrder, hp, hAB hp, hs, hr]
  have hs := Finset.sum_sdiff (f := D) hAB
  unfold tableProfile
  rw [provisional_signedMass, provisional_signedMass]
  change _ + (∑ p ∈ B, D p) = _ + _ + _
  change _ + (∑ p ∈ A, D p) = (∑ p ∈ B, D p) at hs
  linarith only [hmass, hs, holdsum]

end UnconditionalCounterexample.Calibration
