import UnconditionalCounterexample.Hierarchy.WeightedRealization
import UnconditionalCounterexample.Hierarchy.WeightedDomain
import UnconditionalCounterexample.Hierarchy.WeightedQuasiAtomic
import UnconditionalCounterexample.Hierarchy.StrictClasses

/-!
# The quasi-atomic overring and its explicit weight-one obstruction

The selected ring, its primes, the additive weight and the obstructing
element are all taken in the same subring of the rational function field.
-/

noncomputable section
namespace UnconditionalCounterexample.Hierarchy.Weighted

open GuardSupport DiscreteOrders IntersectionDomain Factorization

local instance separationRatAlgebra : Algebra ℚ (RatFunc ℚ) := RatFunc.instAlgebraOfPolynomial ℚ ℚ
private abbrev B := (PoleAlgebra.generated (Set.range selectedPoles)).toSubring
private abbrev v := valuation selectedPlaces

/-- Integral marked weight of an element of the selected ring. -/
def ringWeight (x : selectedRing) : ℚ :=
  profileWeight (fieldProfile selectedPlaces selectedField_hasIntegralProfile (x : RatFunc ℚ))

theorem ringWeight_unit (x : selectedRing) (hx : IsUnit x) : ringWeight x = 0 := by
  have h : fieldProfile selectedPlaces selectedField_hasIntegralProfile (x : RatFunc ℚ) = 0 := by
    ext n y
    exact (fieldProfile_apply ..).trans (order_unit_on_ring B v x hx (.inl (n,y)))
  simp [ringWeight, h]

theorem ringWeight_mul (x y : selectedRing) (hx : x ≠ 0) (hy : y ≠ 0) :
    ringWeight (x*y) = ringWeight x + ringWeight y := by
  unfold ringWeight
  rw [Subring.coe_mul, fieldProfile_mul _ _ _ _ (fun h => hx (Subtype.ext h))
    (fun h => hy (Subtype.ext h)), map_add]

theorem ringWeight_atom (x : selectedRing) (hx : Irreducible x) : ringWeight x = 0 :=
  atom_profileWeight_zero B v selected_unmarked_patch x hx _ (fieldProfile_apply _ _ _)
    (fieldProfile_integral _ _ _)

theorem selected_prime_irreducible (p : ℕ) (hp : p.Prime) : Irreducible (p : selectedRing) := by
  apply prime_irreducible selectedPlaces (Set.range selectedPoles) selectedPrimes_injective _ ⟨p,hp⟩
  intro b hb n x y
  exact selectedPoleUnit_parity (inclusion B v b) hb n x y

/-- Every nonzero element of the selected ring divides an atomic product there. -/
theorem selected_quasiAtomic : IsQuasiAtomicDomain selectedRing := by
  apply quasiAtomic_of_doubled_profiles B v (poleAlgebra_isBFDomain _ ?_) selected_doubled_profiles
    _ selected_prime_irreducible
  · rintro f ⟨n,rfl⟩
    exact (selectedPole_irreducible n).ne_zero
  · intro f hf
    exact clear_of_profile selectedPlaces f hf (fieldProfile _ selectedField_hasIntegralProfile f)
      (fun n x => (fieldProfile_apply _ _ _ n x).symm)

/-- Rational prime below the first selected fiber. -/
def firstPrime : GuardSupport.PrimeIndex := (selectedPlaces 0).prime

theorem exists_weightOne_divisor :
    ∃ b : selectedRing, b ≠ 0 ∧ b ∣ (firstPrime.val : selectedRing)^8 ∧ ringWeight b = 1 := by
  have hq (k : ℕ) (y : Fiber) :
      order (v (.inl (k,y))) (firstPrime.val : RatFunc ℚ) = if k = 0 then 1 else 0 := by
    rw [order_prime]
    simp only [placePrime,firstPrime,selectedPrimes_injective.eq_iff]
  have hg (q : Guard selectedPlaces) : order (v (.inr q)) (firstPrime.val : RatFunc ℚ) = 0 := by
    have h : q.val ≠ firstPrime := fun he => q.property ⟨0,he.symm⟩
    simp [order_prime,placePrime,h]
  obtain ⟨b,hb,hd,hs,hw⟩ := exists_weightOne_dvd_eighth B v (firstPrime.val : selectedRing)
    (Nat.cast_ne_zero.mpr firstPrime.property.ne_zero) hq hg selected_first_patch
  have he : fieldProfile _ selectedField_hasIntegralProfile (b : RatFunc ℚ) =
      Finsupp.single 0 (patch firstPatch 8) := by
    ext n x
    exact (fieldProfile_apply _ _ _ n x).trans (hs n x)
  exact ⟨b,hb,hd, (congrArg profileWeight he).trans hw⟩

theorem selected_not_almostAtomic : ¬ IsAlmostAtomicDomain selectedRing := by
  obtain ⟨b,hb,_,hw⟩ := exists_weightOne_divisor
  exact not_almostAtomic_of_weight ringWeight ringWeight_unit ringWeight_mul ringWeight_atom b hb
    (hw.trans_ne one_ne_zero)

/-- The actual almost Dedekind overring witnessing failure of the converse
to almost atomicity implying quasi-atomicity. -/
theorem weightedWitness : StrictHierarchy.Witness (fun R => IsAlmostAtomicDomain R)
    (fun R => IsQuasiAtomicDomain R) selectedRing :=
  ⟨⟨intZ_le _ _,isAlmostDedekind _ _ selectedPrimes_injective,selected_quasiAtomic⟩,
    selected_not_almostAtomic⟩

end UnconditionalCounterexample.Hierarchy.Weighted
