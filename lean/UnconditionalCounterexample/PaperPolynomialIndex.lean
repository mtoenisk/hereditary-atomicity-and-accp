import UnconditionalCounterexample.PaperCubeChain
import UnconditionalCounterexample.PaperPolynomialPart
import UnconditionalCounterexample.PaperSubrings
import Mathlib.GroupTheory.Index

/-!
# The infinite index of the polynomial part

The first selected raw polynomial has a nonconstant irreducible denominator
in the fraction 8/F₁, which is integral at every vertical place. No positive
multiple of this element belongs to the polynomial part.
-/

noncomputable section
namespace UnconditionalCounterexample.PaperConstruction

open Polynomial WithZero PrimaryWordProfiles IntersectionDomain
local instance : Algebra ℚ (RatFunc ℚ) := RatFunc.instAlgebraOfPolynomial ℚ ℚ

private theorem first_prime : (PrimaryChoices.primes 0).val = 2 := by
  let p : GuardSupport.PrimeIndex := ⟨2,Nat.prime_two⟩
  have h := PrimaryChoices.primes.monotone (Nat.zero_le (PrimaryChoices.primes.symm p))
  rw [PrimaryChoices.primes.apply_symm_apply] at h
  exact le_antisymm h (PrimaryChoices.primes 0).property.two_le

private theorem first_raw_eq : algebraMap ℚ[X] (RatFunc ℚ) (raw 0) = construction.chain.b 0 := by
  change _ = RawWords.normalizedFactor (fun i ↦ algebraMap ℚ[X] (RatFunc ℚ) (raw i)) exponent 0
  simp [RawWords.normalizedFactor]

theorem eight_div_first_raw_mem : (8 : RatFunc ℚ) / algebraMap ℚ[X] (RatFunc ℚ) (raw 0) ∈ domain := by
  apply (div_mem_iff _ _ (map_ne_zero_iff _ (IsFractionRing.injective ℚ[X] (RatFunc ℚ)) |>.mpr
    (construction.chain.raw_irreducible 0).ne_zero)).mpr
  constructor
  · rw [div_eq_mul_inv]
    exact (PoleAlgebra.generated poles).mul_mem ((PoleAlgebra.generated poles).natCast_mem 8)
      (PoleAlgebra.inverse_mem (Set.mem_range_self 0))
  · rw [first_raw_eq]
    rintro (j | p)
    · rw [PaperCubeChain.b_primary]
      by_cases hj : j = 0
      · subst j
        have hp : PairedDomain.vertical places (.inl 0) ((places.primes 0).val : RatFunc ℚ) = exp (-1) :=
          EvaluationDVR.valuation_prime _ _
        rw [show (places.primes 0).val = 2 from first_prime, Nat.cast_ofNat] at hp
        rw [show (8 : RatFunc ℚ) = 2^3 by norm_num,map_pow,hp,← exp_nsmul]
        norm_num [bWeight,nsmul_eq_mul]
      · simpa [bWeight,hj] using valuation_natCast_le_one (PairedDomain.vertical places (.inl j)) 8
    · rw [PaperCubeChain.b_guard]
      exact valuation_natCast_le_one _ 8

/-- The actual element whose class generates an infinite cyclic subgroup of D/A. -/
def polynomialIndexWitness : domain := ⟨_,eight_div_first_raw_mem⟩

@[simp] theorem coe_polynomialIndexWitness :
    (polynomialIndexWitness : RatFunc ℚ) = 8 / algebraMap ℚ[X] (RatFunc ℚ) (raw 0) := rfl

/-- Every positive multiple still has a pole at the first raw polynomial. -/
theorem polynomialIndexWitness_multiple_not_mem (n : ℕ) (hn : 0 < n) :
    n • polynomialIndexWitness ∉ polynomialPart := by
  rintro ⟨f,hf⟩
  let ι := algebraMap ℚ[X] (RatFunc ℚ)
  have hr : ι (raw 0) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective ℚ[X] (RatFunc ℚ))).mpr (construction.chain.raw_irreducible 0).ne_zero
  have h : ι f = (n : RatFunc ℚ) * (8 / ι (raw 0)) := by
    change ι f = domain.subtype (n • polynomialIndexWitness) at hf
    rw [map_nsmul,nsmul_eq_mul] at hf
    exact hf
  rw [← mul_div_assoc,eq_div_iff hr] at h
  have he : f * raw 0 = (n : ℚ[X]) * 8 := by
    apply IsFractionRing.injective ℚ[X] (RatFunc ℚ)
    simpa only [map_mul,map_natCast,map_ofNat] using h
  have hu : IsUnit ((n : ℚ[X]) * 8) := by
    have h := (isUnit_iff_ne_zero.mpr (mul_ne_zero (Nat.cast_ne_zero.mpr hn.ne') (by norm_num : (8 : ℚ) ≠ 0))).map (Polynomial.C : ℚ →+* ℚ[X])
    simpa only [map_mul,map_natCast,map_ofNat] using h
  exact (construction.chain.raw_irreducible 0).not_isUnit (isUnit_of_dvd_unit ⟨f,he.symm.trans (mul_comm ..)⟩ hu)

/-- The class of the explicit witness has infinite additive order. -/
theorem polynomialIndexWitness_infiniteOrder :
    ¬ IsOfFinAddOrder (polynomialIndexWitness : domain ⧸ polynomialPart.toAddSubgroup) := by
  rintro h
  obtain ⟨n,hn,he⟩ := isOfFinAddOrder_iff_nsmul_eq_zero.mp h
  rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff] at he
  exact polynomialIndexWitness_multiple_not_mem n hn he

/-- No nonzero integer multiple of the actual fraction 8/F₁ lies in A. -/
theorem polynomialIndexWitness_zsmul_not_mem (z : ℤ) (hz : z ≠ 0) :
    z • polynomialIndexWitness ∉ polynomialPart := by
  intro h
  let x : domain ⧸ polynomialPart.toAddSubgroup := polynomialIndexWitness
  have hi : Function.Injective (fun m : ℤ ↦ m • x) :=
    injective_zsmul_iff_not_isOfFinAddOrder.mpr polynomialIndexWitness_infiniteOrder
  apply hz
  apply hi
  change z • x = (0 : ℤ) • x
  rw [zero_zsmul]
  exact (QuotientAddGroup.mk_zsmul polynomialPart.toAddSubgroup polynomialIndexWitness z).symm.trans
    ((QuotientAddGroup.eq_zero_iff _).mpr h)

theorem polynomialPart_quotient_infinite : Infinite (domain ⧸ polynomialPart.toAddSubgroup) :=
  Infinite.of_injective _ (injective_nsmul_iff_not_isOfFinAddOrder.mpr polynomialIndexWitness_infiniteOrder)

theorem polynomialPart_infiniteIndex : ¬ polynomialPart.toAddSubgroup.FiniteIndex := by
  intro h
  exact (not_finite_iff_infinite.mpr polynomialPart_quotient_infinite) (AddSubgroup.finiteIndex_iff_finite_quotient.mp h)

/-- The infinite-index case of the classification applies to every subring of A. -/
theorem polynomialPart_hereditarilyBF : Factorization.IsHereditarilyBF polynomialPart :=
  infinite_quotient_hereditarilyBF polynomialPart polynomialPart_quotient_infinite

end UnconditionalCounterexample.PaperConstruction
