import UnconditionalCounterexample.Variations.DyadicRawRows
import UnconditionalCounterexample.Variations.DyadicRawOrders
import UnconditionalCounterexample.Variations.DyadicFiniteProfiles

/-!
# The actual normalized generators translate by their exact dyadic columns

The full valuation table has zero entries on guards and retained horizontal
primes. On primaries it has precisely the balanced, adjacent and auxiliary
columns of the formal elimination.
-/

noncomputable section
namespace UnconditionalCounterexample.Variations.DyadicLedger.Calibrated

open GuardSupport Univariate DyadicDeviations FieldGeneration DiscreteOrders WithZero
open DyadicEscape (Generator)

variable (a : Policy)

def auxiliaryPrime : (Σ k, Aux a k) ↪ PrimeIndex where
  toFun j := j.2.prime
  inj' := by
    intro i j h
    have hi : guardPrime a (.inr (.inr (.inl i))) = guardPrime a (.inr (.inr (.inl j))) := h
    exact Sum.inl.inj (Sum.inr.inj (Sum.inr.inj ((guardPrime a).injective hi)))

abbrev auxIndex (k : Bool) (j : Aux a k) := j.index
abbrev auxPositive (k : Bool) (j : Aux a k) := j.positive
abbrev actualRow (n : ℕ) : Coordinates a → ℤ :=
  rawRow (auxiliaryPrime a) (auxIndex a) (auxPositive a) (fun c k i => regularPrime a (c,k,i))
    ((driver a).actualRequest n).column

theorem column_is_basis (n : ℕ) :
    ∃ g : Generator ⊕ (Σ k, Aux a k), basisLabel (auxiliaryPrime a) (auxIndex a) (auxPositive a) g =
      ((driver a).actualRequest n).column := by
  let D := driver a
  rcases (emission a).exhaustive n with ⟨r,j,_,hc⟩ | ⟨g,_,h⟩
  · obtain ⟨p,k,i,b,hp,he,hr⟩ := (recorded a).allocated r _ (List.getElem_mem (h := j.isLt))
    let t : Aux a k := ⟨p,i,b,(D.permanentRole_requested p hp).trans hr⟩
    exact ⟨.inr ⟨k,t⟩,(hc.trans he).symm⟩
  · refine ⟨.inl g, ?_⟩
    cases g <;> exact h.symm

private theorem generator_guard_order (n : ℕ) (g : GuardIndex (Aux a) (Lone a)) :
    order (guardVal a g) (generatorUnit (driver a) n).val = 0 := by
  let D := driver a
  let p := guardPrime a g
  rw [evaluation_order]
  change (UnivariateExtraction.guardHom D.requirements p ((chain D.requirements).generators n)).valuation = 0
  rw [← UnivariateExtraction.eval_permanent_guard]
  let φ := (permanentSite D.requirements p).evaluate true (Or.inl rfl)
  change (φ ((chain D.requirements).generators n)).valuation = 0
  have hn : φ ((chain D.requirements).generators n) ≠ 0 :=
    (map_ne_zero φ).mpr ((chain D.requirements).generators_ne_zero n)
  simpa using EvaluationChoices.valuation_eq_of_norm_eq p.val hn (one_ne_zero : (1 : ℚ_[p.val]) ≠ 0)
    ((D.generator_guard_norm_one n p).trans norm_one.symm)

/-- The complete coordinate order, with the two primaries of every balanced
column and the signed correction on each actual auxiliary prime. -/
theorem generator_order (n : ℕ) (i : Coordinates a) :
    order (valuation a i) (generatorUnit (driver a) n).val = actualRow a n i := by
  let D := driver a
  rcases i with ⟨c⟩ | ⟨k,j⟩ | ⟨k,j⟩ | ⟨i⟩
  · exact centre_order_generator a c n
  · change order (regularVal a (false,k,j)) _ = _
    rw [regularVal,primaryVal,evaluation_order]
    exact generator_primary_order a n _ _ (regularPrime_role a (false,k,j))
  · change order (regularVal a (true,k,j)) _ = _
    rw [regularVal,primaryVal,evaluation_order]
    exact generator_primary_order a n _ _ (regularPrime_role a (true,k,j))
  · cases i with
    | auxiliary k j =>
      change order (auxVal a k j) _ = _
      rw [auxVal,primaryVal,evaluation_order]
      exact generator_primary_order a n _ _ j.role_eq
    | plusGuard k j => exact generator_guard_order a n (.inl (k,j))
    | minusGuard k j => exact generator_guard_order a n (.inr (.inl (k,j)))
    | auxiliaryGuard k j => exact generator_guard_order a n (.inr (.inr (.inl ⟨k,j⟩)))
    | loneGuard g => exact generator_guard_order a n (.inr (.inr (.inr g)))
    | horizontal q =>
      apply (order_eq_zero_iff _ (generatorUnit D n).ne_zero).mpr
      apply AtomProfiles.generators_horizontal_valuation _ _ _ _ _ n
      · exact fun i => ((chain D.requirements).raw_monic i).ne_zero
      · exact (HorizontalOrders.retained_range_iff _ (fun j => ⟨(chain D.requirements).raw_monic j,
          (chain D.requirements).raw_irreducible j⟩) q.val).mpr q.property.1

/-- Actual multiplication by the stage generator gives the literal
singleton sum in the profile action. -/
theorem generator_translates (signed : (RatFunc ℚ)ˣ → Profile (Aux a) (Lone a) (Horiz a))
    (hval : ∀ y i, (signed y).signedValues i = order (valuation a i) y.val)
    (n : ℕ) (x : (RatFunc ℚ)ˣ) :
    signed (x * generatorUnit (driver a) n) = (signed x).translate (auxIndex a) (auxSign (auxPositive a))
      (columnsOfRaw (auxiliaryPrime a) (auxIndex a) (auxPositive a) (Finsupp.single ((driver a).actualRequest n).column 1)) := by
  apply Profile.signedValues_injective
  funext i
  rw [hval,Units.val_mul,order_mul _ x.ne_zero (generatorUnit (driver a) n).ne_zero,generator_order,← hval]
  obtain ⟨g,hg⟩ := column_is_basis a n
  have hrow := rowChange_eq_rawRow (auxiliaryPrime a) (auxIndex a) (auxPositive a)
    (fun c k j => regularPrime a (c,k,j)) (signed x) g i
  dsimp only at hrow
  rw [hg] at hrow
  change _ - (signed x).signedValues i = actualRow a n i at hrow
  omega

end UnconditionalCounterexample.Variations.DyadicLedger.Calibrated
