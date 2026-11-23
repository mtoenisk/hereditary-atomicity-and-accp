import UnconditionalCounterexample.Variations.MultiDomainPlaces
import UnconditionalCounterexample.Variations.GuardUnramified
import UnconditionalCounterexample.IntersectionStalks

/-! # Finite vertical residue fields

Restriction of a valuation induces an embedding of residue fields.
In the unramified guard model the valuation ring is the Witt integer ring,
whose residue field is the prescribed finite field.
-/

noncomputable section
namespace UnconditionalCounterexample.Variations.MultiDomain

open GuardSupport WithZero IntersectionStalks IntersectionDomain IsLocalRing

/-- A normalized prime gives the restricted valuation ring its DVR structure. -/
theorem isDVR_of_prime_value {K : Type*} [Field K] (v : Valuation K ℤᵐ⁰)
    {p : ℕ} (hp : v (p : K) = exp (-1)) : IsDiscreteValuationRing v.valuationSubring := by
  let : v.IsNontrivial := ⟨p, by rw [hp]; exact exp_ne_zero, by rw [hp]; decide⟩
  infer_instance

/-- Rational primes different from the residue characteristic are units. -/
theorem other_prime_value {K : Type*} [Field K] (v : Valuation K ℤᵐ⁰) (p q : PrimeIndex)
    (hp : v (p.val : K) = exp (-1)) (hq : p ≠ q) : v (q.val : K) = 1 := by
  let V := v.valuationSubring
  let k := ResidueField V
  have hz (n : ℕ) : (n : k) = 0 ↔ v (n : K) < 1 := by
    rw [← map_natCast (residue V), residue_eq_zero_iff]
    exact Valuation.mem_maximalIdeal_iff K v
  let : CharP k p.val := (CharP.charP_iff_prime_eq_zero p.property).mpr
    ((hz p.val).mpr (by rw [hp, exp_lt_one_iff]; decide))
  exact (valuation_natCast_le_one v _).antisymm (le_of_not_gt fun h =>
    CharP.cast_ne_zero_of_ne_of_prime k q.property (fun he => hq (Subtype.ext he)) ((hz q.val).mpr h))

/-- A restricted valuation has finite residue field whenever the ambient one does. -/
theorem finite_residue_comap {K L : Type*} [Field K] [Field L] (v : Valuation L ℤᵐ⁰)
    [Finite (ResidueField v.valuationSubring)] (e : K →+* L) :
    Finite (ResidueField (v.comap e).valuationSubring) := by
  let W := (v.comap e).valuationSubring
  let m : W →+* v.valuationSubring :=
    (e.comp W.subtype).codRestrict v.valuationSubring.toSubring fun x => x.property
  let f := (residue v.valuationSubring).comp m
  have hk : RingHom.ker f = maximalIdeal W := by
    ext x
    exact (residue_eq_zero_iff (m x)).trans ((Valuation.mem_maximalIdeal_iff L v).trans
      (Valuation.mem_maximalIdeal_iff K (v.comap e)).symm)
  let g := f.kerLift.comp (Ideal.quotEquivOfEq hk.symm).toRingHom
  exact Finite.of_injective g (f.kerLift_injective.comp (Ideal.quotEquivOfEq hk.symm).injective)

/-- The valuation ring of the finite unramified local model has finite residue field. -/
theorem finite_witt_residue (p : ℕ) [Fact p.Prime] (k : Type*) [Field k] [CharP k p]
    [Finite k] [Algebra (ZMod p) k] :
    Finite (ResidueField (GuardUnramified.valuation p k).valuationSubring) := by
  let W := WittVector p k
  let v := GuardUnramified.valuation p k
  let h : W →+* v.valuationSubring := (algebraMap W (GuardUnramified.LocalField p k)).codRestrict
    v.valuationSubring.toSubring fun x => (GuardUnramified.integral_iff p k _).mpr ⟨x,rfl⟩
  have hi : Function.Injective h := fun _ _ he => IsFractionRing.injective W _
    (congrArg Subtype.val he)
  have hs : Function.Surjective h := fun x => by
    obtain ⟨w,hw⟩ := (GuardUnramified.integral_iff p k x).mp x.property
    exact ⟨w,Subtype.ext hw⟩
  let c : W →+* k := WittVector.constantCoeff
  have hc : RingHom.ker c = maximalIdeal W :=
    WittVector.ker_constantCoeff.trans
      ((IsDiscreteValuationRing.irreducible_iff_uniformizer (p : W)).mp (WittVector.irreducible p)).symm
  let e := (ResidueField.mapEquiv (RingEquiv.ofBijective h ⟨hi,hs⟩)).symm
  let t := (Ideal.quotEquivOfEq hc.symm).trans
    (RingHom.quotientKerEquivOfSurjective (WittVector.constantCoeff_surjective p))
  exact Finite.of_injective _ (t.injective.comp e.injective)

/-- The image of the ordinary intersection in a finite residue field is itself a field. -/
theorem maximal_center_of_finite_residue {K ι : Type*} [Field K]
    (B : Subring K) (v : ι → Valuation K ℤᵐ⁰) (i : ι)
    [Finite (ResidueField (v i).valuationSubring)] : (center B v i).IsMaximal := by
  let f := (residue (v i).valuationSubring).comp (valuationInclusion B v i)
  have hk : RingHom.ker f = center B v i := by
    rw [← RingHom.comap_ker, ker_residue]
    rfl
  rw [← hk]
  let : (RingHom.ker f).IsPrime := RingHom.ker_isPrime f
  let : Finite (_ ⧸ RingHom.ker f) := Finite.of_injective _ f.kerLift_injective
  exact Ideal.Quotient.maximal_of_isField _ (Finite.isField_of_domain _)

namespace Places
variable {r : ℕ} (P : Places r) (F : ℕ → Polys r) (hF : ∀ n, F n ≠ 0)

/-- Both the p-adic primary and finite-residue guard centres are maximal. -/
theorem centers_maximal
    (hg : ∀ p, Finite (ResidueField (P.guardVal p).valuationSubring)) (i : ℕ ⊕ PrimeIndex) :
    (center (poleAlgebra (P.data F hF)).toSubring (vertical (P.data F hF)) i).IsMaximal := by
  cases i with
  | inl j =>
    exact center_isMaximal_of_residueMap _ _ _ (P.primes j).val
      (EvaluationDVR.residueMap _ (IndependentTuples.evaluation (P.primary j).x (P.primary j).independent))
      (EvaluationDVR.residueMap_ker _ _)
  | inr p =>
    let := hg p
    let : Finite (ResidueField ((vertical (P.data F hF)) (.inr p)).valuationSubring) :=
      finite_residue_comap (P.guardVal p) (IndependentTuples.evaluation (P.guard p).x (P.guard p).independent)
    exact maximal_center_of_finite_residue _ _ _

end Places
end UnconditionalCounterexample.Variations.MultiDomain
