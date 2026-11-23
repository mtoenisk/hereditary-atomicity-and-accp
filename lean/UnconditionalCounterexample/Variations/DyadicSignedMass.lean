import UnconditionalCounterexample.Variations.DyadicSignedField
import UnconditionalCounterexample.Variations.DyadicHorizontalMass
import UnconditionalCounterexample.Variations.DyadicGeneratorColumns

/-! # Both principal mass equations for every rational function field unit -/

noncomputable section
namespace UnconditionalCounterexample.Variations.DyadicLedger.Calibrated
open DyadicDeviations DiscreteOrders FieldGeneration

variable (a : Policy)

/-- A normalized generator translates the unit profile by its literal
R, Q or S column, which preserves both masses and both centre heights. -/
theorem generator_mass (n : ℕ) :
    (signed a (generatorUnit (driver a) n)).MassEquations (auxIndex a) (auxSign (auxPositive a)) := by
  have h1 : (signed a 1).MassEquations (auxIndex a) (auxSign (auxPositive a)) :=
    scalar_physical_mass a 1 one_ne_zero (signed a 1) (fun i => by simpa using signed_values a 1 i)
  have h := generator_translates a (signed a) (signed_values a) n 1
  rw [one_mul] at h
  rw [h]
  intro k
  rw [Profile.translate, Profile.signedMass_addColumns]
  exact h1 k

/-- The calibrated driver, including its choice of split policy, gives
the two required mass equations on the entire rational function field. -/
theorem signed_mass (u : (RatFunc ℚ)ˣ) :
    (signed a u).MassEquations (auxIndex a) (auxSign (auxPositive a)) := by
  apply Profile.mass_all (driver a) (signed a) _ _ _ _ _ (generator_mass a) u
  · intro x y i
    simp only [signed_values, Units.val_mul, order_mul _ x.ne_zero y.ne_zero]
  · intro q hq
    exact scalar_physical_mass a q hq _ (signed_values a (scalarUnit q hq))
  · intro f hf
    exact retained_physical_mass a f hf _ (signed_values a (horizontalUnit f))

end UnconditionalCounterexample.Variations.DyadicLedger.Calibrated
