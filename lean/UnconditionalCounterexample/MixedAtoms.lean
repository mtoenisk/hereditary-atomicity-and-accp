import UnconditionalCounterexample.MixedGeneratorProfiles
import UnconditionalCounterexample.SparseAtoms
import UnconditionalCounterexample.SparseUnitSigns
import UnconditionalCounterexample.ReturnChain

/-! Complete profiles and literal recurrence atoms for each actual infinite selected-prime family. -/

namespace UnconditionalCounterexample.MixedConstruction

open SparseProfiles SparseAtoms

variable (S : Set GuardSupport.PrimeIndex) (hS : S.Infinite)

private theorem rawFacts (i : ℕ) : ((raw S hS) i).Monic ∧ Irreducible ((raw S hS) i) :=
  ⟨(construction S hS).chain.raw_monic i, (construction S hS).chain.raw_irreducible i⟩

private theorem rawInj : Function.Injective (raw S hS) :=
  fun _ _ h => (construction S hS).chain.raw_degree_strict.injective (congrArg Polynomial.natDegree h)

/-- The complete actual profile on the actual sparse constructed domain. -/
noncomputable def valuationProfiles : ValuationProfiles (domain S hS) (Outside (poles S hS)) :=
  profiles (raw S hS) (rawFacts S hS) (rawInj S hS) (construction S hS).chain.raw_constant_ne_zero (exponent S hS) (places S hS)
    (MixedGeneratorProfiles.generatorProfiles S hS) (guardSupport S hS)

theorem valuationProfiles_cast (p : ProfilePlace (Outside (poles S hS))) (x : (domain S hS)) (hx : x ≠ 0) :
    ((valuationProfiles S hS).value p x : ℤ) = DiscreteOrders.order (valuations (poles S hS) (places S hS) p) (x : RatFunc ℚ) :=
  profiles_value_cast (raw S hS) (rawFacts S hS) (rawInj S hS) (construction S hS).chain.raw_constant_ne_zero (exponent S hS) (places S hS)
    (MixedGeneratorProfiles.generatorProfiles S hS) (guardSupport S hS) p x hx

theorem valuationProfiles_limit_cast (x : (domain S hS)) (hx : x ≠ 0) :
    ((valuationProfiles S hS).value .limit x : ℤ) = PrimaryStabilization.tOrder (x : RatFunc ℚ) :=
  profiles_limit_cast (raw S hS) (rawFacts S hS) (rawInj S hS) (construction S hS).chain.raw_constant_ne_zero (exponent S hS) (places S hS)
    (MixedGeneratorProfiles.generatorProfiles S hS) (guardSupport S hS) x hx

theorem coordinate_divisibility (x y : (domain S hS)) (hx : x ≠ 0) (hy : y ≠ 0)
    (hle : ∀ p, (valuationProfiles S hS).value p x ≤ (valuationProfiles S hS).value p y) : x ∣ y :=
  SparseProfiles.coordinate_divisibility (raw S hS) (rawFacts S hS) (rawInj S hS) (construction S hS).chain.raw_constant_ne_zero
    (exponent S hS) (places S hS) (MixedGeneratorProfiles.generatorProfiles S hS) (guardSupport S hS) x y hx hy hle

theorem signedDifferenceTriple : ValuationProfiles.SignedDifferenceTriple (valuationProfiles S hS) :=
  SparseProfiles.signedDifferenceTriple (raw S hS) (rawFacts S hS) (rawInj S hS) (construction S hS).chain.raw_constant_ne_zero
    (exponent S hS) (places S hS) (MixedGeneratorProfiles.generatorProfiles S hS) (guardSupport S hS)

theorem finite_associates_divisors_of_order_le_one (x : (domain S hS)) (hx : x ≠ 0)
    (horder : PrimaryStabilization.tOrder (x : RatFunc ℚ) ≤ 1) :
    {a : Associates (domain S hS) | a ∣ Associates.mk x}.Finite :=
  SparseProfiles.finite_associates_divisors_of_order_le_one (raw S hS) (rawFacts S hS) (rawInj S hS)
    (construction S hS).chain.raw_constant_ne_zero (exponent S hS) (places S hS) (MixedGeneratorProfiles.generatorProfiles S hS) (guardSupport S hS) x hx horder

theorem isUnit_iff_sign (x : (domain S hS)) : IsUnit x ↔ x = 1 ∨ x = -1 :=
  SparseUnitSigns.isUnit_iff_eq_one_or_neg_one (raw S hS) (rawFacts S hS) (rawInj S hS) (construction S hS).chain.raw_constant_ne_zero
    (exponent S hS) (places S hS) (MixedGeneratorProfiles.generatorProfiles S hS) x

theorem subring_reflects_units (T : Subring (domain S hS)) (x : T) : IsUnit (x : (domain S hS)) → IsUnit x :=
  UnitSigns.subring_reflects_units (fun y hy => (isUnit_iff_sign S hS y).mp hy) T x

/-- The actual recurrence in the constructed ring, with no existential choice of elements. -/
noncomputable def atom (n : ℕ) : (domain S hS) :=
  aElement (raw S hS) (exponent S hS) (places S hS) (MixedGeneratorProfiles.generatorProfiles S hS) (SparsePrimaryDomain.ofSelected_primary_zero S hS _ _)
    (construction S hS).chain.guardChain.value_unit n

@[simp] theorem coe_atom (n : ℕ) : ((atom S hS) n : RatFunc ℚ) = (construction S hS).chain.a n := rfl

@[simp] theorem coe_atom_zero : ((atom S hS) 0 : RatFunc ℚ) = RatFunc.X := rfl

theorem atom_ne_zero (n : ℕ) : (atom S hS) n ≠ 0 :=
  aElement_ne_zero (raw S hS) (exponent S hS) (places S hS) (MixedGeneratorProfiles.generatorProfiles S hS) (SparsePrimaryDomain.ofSelected_primary_zero S hS _ _)
    (construction S hS).chain.guardChain.value_unit (fun j => ((rawFacts S hS) j).1.ne_zero) n

theorem atom_primary (n j : ℕ) :
    ((valuationProfiles S hS).value (.primary j) ((atom S hS) n) : ℤ) = primaryAtomProfile n j :=
  aElement_primary (raw S hS) (rawFacts S hS) (rawInj S hS) (construction S hS).chain.raw_constant_ne_zero (exponent S hS) (places S hS)
    (MixedGeneratorProfiles.generatorProfiles S hS) (SparsePrimaryDomain.ofSelected_primary_zero S hS _ _) (construction S hS).chain.guardChain.value_unit (guardSupport S hS) n j

theorem atom_limit (n : ℕ) : (valuationProfiles S hS).value .limit ((atom S hS) n) = 1 :=
  aElement_limit (raw S hS) (rawFacts S hS) (rawInj S hS) (construction S hS).chain.raw_constant_ne_zero (exponent S hS) (places S hS)
    (MixedGeneratorProfiles.generatorProfiles S hS) (SparsePrimaryDomain.ofSelected_primary_zero S hS _ _) (construction S hS).chain.guardChain.value_unit (guardSupport S hS) n

theorem atom_outside (n : ℕ) (i : Outside (poles S hS)) : (valuationProfiles S hS).value (.outside i) ((atom S hS) n) = 0 :=
  aElement_outside (raw S hS) (rawFacts S hS) (rawInj S hS) (construction S hS).chain.raw_constant_ne_zero (exponent S hS) (places S hS)
    (MixedGeneratorProfiles.generatorProfiles S hS) (SparsePrimaryDomain.ofSelected_primary_zero S hS _ _) (construction S hS).chain.guardChain.value_unit (guardSupport S hS) n i

theorem atom_guard_valuation (n : ℕ) (p : GuardSupport.PrimeIndex) :
    SparsePrimaryDomain.vertical (places S hS) (.inr p) ((atom S hS) n : RatFunc ℚ) = 1 :=
  a_guard (raw S hS) (exponent S hS) (places S hS) (MixedGeneratorProfiles.generatorProfiles S hS) (construction S hS).chain.guardChain.value_unit n p

theorem atom_tOrder (n : ℕ) : PrimaryStabilization.tOrder ((atom S hS) n : RatFunc ℚ) = 1 := by
  rw [← (valuationProfiles_limit_cast S hS) _ ((atom_ne_zero S hS) n), (atom_limit S hS)]
  rfl

theorem atom_irreducible (n : ℕ) : Irreducible ((atom S hS) n) :=
  aElement_irreducible (raw S hS) (rawFacts S hS) (rawInj S hS) (construction S hS).chain.raw_constant_ne_zero (exponent S hS) (places S hS)
    (MixedGeneratorProfiles.generatorProfiles S hS) (SparsePrimaryDomain.ofSelected_primary_zero S hS _ _) (construction S hS).chain.guardChain.value_unit (guardSupport S hS) n

end UnconditionalCounterexample.MixedConstruction
