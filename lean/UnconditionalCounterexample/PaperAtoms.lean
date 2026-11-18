import UnconditionalCounterexample.AtomProfiles
import UnconditionalCounterexample.PaperValuations
import UnconditionalCounterexample.UnitSigns
import UnconditionalCounterexample.ReturnChain

/-!
# Complete profiles and atoms of the single constructed domain

Every hypothesis of the profile, unit-sign and atom calculations is supplied by
the actual simultaneous PaperConstruction sequence. The atoms are the literal
return recurrence in that same sequence, beginning at the rational variable X.
-/

namespace UnconditionalCounterexample.PaperConstruction

open CompleteProfiles AtomProfiles

private theorem rawFacts (i : ℕ) : (raw i).Monic ∧ Irreducible (raw i) :=
  ⟨construction.chain.raw_monic i, construction.chain.raw_irreducible i⟩

private theorem rawInj : Function.Injective raw :=
  fun _ _ h => construction.chain.raw_degree_strict.injective (congrArg Polynomial.natDegree h)

/-- The complete actual profile on the single constructed domain. -/
noncomputable def valuationProfiles : ValuationProfiles domain (Outside poles) :=
  profiles raw rawFacts rawInj construction.chain.raw_constant_ne_zero exponent places
    generatorProfiles guardSupport

theorem valuationProfiles_cast (p : ProfilePlace (Outside poles)) (x : domain) (hx : x ≠ 0) :
    (valuationProfiles.value p x : ℤ) = DiscreteOrders.order (valuations poles places p) (x : RatFunc ℚ) :=
  profiles_value_cast raw rawFacts rawInj construction.chain.raw_constant_ne_zero exponent places
    generatorProfiles guardSupport p x hx

theorem valuationProfiles_limit_cast (x : domain) (hx : x ≠ 0) :
    (valuationProfiles.value .limit x : ℤ) = PrimaryStabilization.tOrder (x : RatFunc ℚ) :=
  profiles_limit_cast raw rawFacts rawInj construction.chain.raw_constant_ne_zero exponent places
    generatorProfiles guardSupport x hx

theorem coordinate_divisibility (x y : domain) (hx : x ≠ 0) (hy : y ≠ 0)
    (hle : ∀ p, valuationProfiles.value p x ≤ valuationProfiles.value p y) : x ∣ y :=
  CompleteProfiles.coordinate_divisibility raw rawFacts rawInj construction.chain.raw_constant_ne_zero
    exponent places generatorProfiles guardSupport x y hx hy hle

theorem signedDifferenceTriple : ValuationProfiles.SignedDifferenceTriple valuationProfiles :=
  CompleteProfiles.signedDifferenceTriple raw rawFacts rawInj construction.chain.raw_constant_ne_zero
    exponent places generatorProfiles guardSupport

theorem finite_associates_divisors_of_order_le_one (x : domain) (hx : x ≠ 0)
    (horder : PrimaryStabilization.tOrder (x : RatFunc ℚ) ≤ 1) :
    {a : Associates domain | a ∣ Associates.mk x}.Finite :=
  CompleteProfiles.finite_associates_divisors_of_order_le_one raw rawFacts rawInj
    construction.chain.raw_constant_ne_zero exponent places generatorProfiles guardSupport x hx horder

theorem isUnit_iff_sign (x : domain) : IsUnit x ↔ x = 1 ∨ x = -1 :=
  UnitSigns.isUnit_iff_eq_one_or_neg_one raw rawFacts rawInj construction.chain.raw_constant_ne_zero
    exponent places generatorProfiles x

theorem subring_reflects_units (T : Subring domain) (x : T) : IsUnit (x : domain) → IsUnit x :=
  UnitSigns.subring_reflects_units (fun y hy => (isUnit_iff_sign y).mp hy) T x

/-- The actual recurrence in the constructed ring, with no existential choice of elements. -/
noncomputable def atom (n : ℕ) : domain :=
  aElement raw exponent places generatorProfiles PrimaryChoices.primary_zero
    construction.chain.guardChain.value_unit n

@[simp] theorem coe_atom (n : ℕ) : (atom n : RatFunc ℚ) = construction.chain.a n := rfl

@[simp] theorem coe_atom_zero : (atom 0 : RatFunc ℚ) = RatFunc.X := rfl

theorem atom_ne_zero (n : ℕ) : atom n ≠ 0 :=
  aElement_ne_zero raw exponent places generatorProfiles PrimaryChoices.primary_zero
    construction.chain.guardChain.value_unit (fun j => (rawFacts j).1.ne_zero) n

theorem atom_primary (n j : ℕ) :
    (valuationProfiles.value (.primary j) (atom n) : ℤ) = primaryAtomProfile n j :=
  aElement_primary raw rawFacts rawInj construction.chain.raw_constant_ne_zero exponent places
    generatorProfiles PrimaryChoices.primary_zero construction.chain.guardChain.value_unit guardSupport n j

theorem atom_limit (n : ℕ) : valuationProfiles.value .limit (atom n) = 1 :=
  aElement_limit raw rawFacts rawInj construction.chain.raw_constant_ne_zero exponent places
    generatorProfiles PrimaryChoices.primary_zero construction.chain.guardChain.value_unit guardSupport n

theorem atom_outside (n : ℕ) (i : Outside poles) : valuationProfiles.value (.outside i) (atom n) = 0 :=
  aElement_outside raw rawFacts rawInj construction.chain.raw_constant_ne_zero exponent places
    generatorProfiles PrimaryChoices.primary_zero construction.chain.guardChain.value_unit guardSupport n i

theorem atom_guard_valuation (n : ℕ) (p : GuardSupport.PrimeIndex) :
    PairedDomain.vertical places (.inr p) (atom n : RatFunc ℚ) = 1 :=
  a_guard raw exponent places generatorProfiles construction.chain.guardChain.value_unit n p

theorem atom_tOrder (n : ℕ) : PrimaryStabilization.tOrder (atom n : RatFunc ℚ) = 1 := by
  rw [← valuationProfiles_limit_cast _ (atom_ne_zero n), atom_limit]
  rfl

theorem atom_irreducible (n : ℕ) : Irreducible (atom n) :=
  aElement_irreducible raw rawFacts rawInj construction.chain.raw_constant_ne_zero exponent places
    generatorProfiles PrimaryChoices.primary_zero construction.chain.guardChain.value_unit guardSupport n

end UnconditionalCounterexample.PaperConstruction
