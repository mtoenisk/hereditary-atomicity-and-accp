import UnconditionalCounterexample.Variations.DyadicDeviations

/-! # Extending a signed profile at fresh calibration sites -/

noncomputable section
namespace UnconditionalCounterexample.Calibration

open DyadicColumns DyadicDeviations

variable {J : Bool → Type*} {G H : Type*}

/-- Embed all previously assigned auxiliary coordinates in the enlarged
index types. The fresh guards have value zero. -/
def extendProfile (p : Profile J G H) (l : Bool → ℤ) : Profile (fun k => Option (J k)) G H where
  height := p.height
  plusDeviation := p.plusDeviation
  minusDeviation := p.minusDeviation
  auxiliary k := Finsupp.mapDomain some (p.auxiliary k) + Finsupp.single none (l k)
  guards := { plus := p.guards.plus
              minus := p.guards.minus
              auxiliary := fun k => Finsupp.mapDomain some (p.guards.auxiliary k)
              lone := p.guards.lone }
  horizontal := p.horizontal

private theorem transfer_old {I : Type*} (index : I → ℕ) (sign : I → ℤ) (i : ℕ) (e : ℤ)
    (u : I →₀ ℤ) :
    auxiliaryTransfer (fun j => j.elim i index) (fun j => j.elim e sign)
      (Finsupp.mapDomain some u) = auxiliaryTransfer index sign u := by
  induction u using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb => rw [Finsupp.mapDomain_add, map_add, map_add, ha, hb]
  | single j z =>
    rw [Finsupp.mapDomain_single]
    simp [auxiliaryTransfer]

/-- Exactly the signed value of the fresh primary is added. This applies
to zero value as well, so unchanged channels require no calibration. -/
theorem signedMass_extendProfile (p : Profile J G H) (index : (k : Bool) → J k → ℕ)
    (sign : (k : Bool) → J k → ℤ) (i : Bool → ℕ) (e l : Bool → ℤ) (k : Bool) :
    (extendProfile p l).signedMass (fun b j => j.elim (i b) (index b))
      (fun b j => j.elim (e b) (sign b)) k =
      p.signedMass index sign k + ((l k * e k : ℤ) : ℚ) * DyadicProfiles.weight (i k) := by
  let Φ := auxiliaryTransfer (fun j : Option (J k) => j.elim (i k) (index k))
    (fun j : Option (J k) => j.elim (e k) (sign k))
  have hsingle : Φ (Finsupp.single none (l k)) = Finsupp.single (i k) (l k * e k) := by
    simp [Φ, auxiliaryTransfer]
  unfold Profile.signedMass
  change p.regularMass k - mass (p.guards.plus k - p.guards.minus k) +
    mass (Φ (Finsupp.mapDomain some (p.auxiliary k) + Finsupp.single none (l k) -
      Finsupp.mapDomain some (p.guards.auxiliary k))) = _
  rw [map_sub Φ, map_add Φ, hsingle,
    transfer_old (index k) (sign k) (i k) (e k) (p.auxiliary k),
    transfer_old (index k) (sign k) (i k) (e k) (p.guards.auxiliary k)]
  simp only [map_sub, map_add, mass_single, DyadicProfiles.weight, DyadicProfiles.tailWeight]
  ring

end UnconditionalCounterexample.Calibration
