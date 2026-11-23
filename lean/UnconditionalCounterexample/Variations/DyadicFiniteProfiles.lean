import UnconditionalCounterexample.Variations.DyadicConcreteCoordinates
import UnconditionalCounterexample.Variations.DyadicFieldGeneration
import UnconditionalCounterexample.AtomProfiles

/-!
# Finite vertical deviations on the actual field

Outside finitely many rational primes a polynomial frozen by the scheduler
has its centre height at regular primaries and has zero order at auxiliary
primaries. Constants are controlled by their scalar prime support. Normalized
generators have the finite support of their single column.
-/

noncomputable section
namespace UnconditionalCounterexample.Variations.DyadicLedger.Calibrated
open Polynomial GuardSupport Univariate FreezingCalendar DiscreteOrders DyadicDeviations WithZero
open FieldGeneration OpeningCalibration

variable (a : Policy)

def regDev (c k : Bool) (x : (RatFunc ℚ)ˣ) (i : ℕ) : ℤ :=
  order (regularVal a (c,k,i)) x.val - order (HorizontalOrders.valuation (centre c)) x.val

def auxOrder (k : Bool) (x : (RatFunc ℚ)ˣ) (j : Aux a k) : ℤ := order (auxVal a k j) x.val

theorem evaluation_order {p : PrimeIndex} (e : RatFunc ℚ →+* ℚ_[p.val]) (x : (RatFunc ℚ)ˣ) :
    order (EvaluationDVR.valuation p.val e) x.val = (e x.val).valuation := by
  have hne : e x.val ≠ 0 := (map_ne_zero e).mpr x.ne_zero
  change -log (Padic.mulValuation (e x.val)) = _
  simp [Padic.mulValuation_toFun,hne]

private theorem centre_factor (c : Bool) :
    (centre c).val = RegularForecast.centreFactor (if c then 1 else 0) := by
  cases c <;> simp [centre,zeroPoint,onePoint,RegularForecast.centreFactor]

theorem centre_order_horizontal (c : Bool) (f : Horizontal) :
    order (HorizontalOrders.valuation (centre c)) (horizontalUnit f).val = height f.val c := by
  change order (HorizontalOrders.valuation (centre c)) (PrincipalProfiles.factor f) = _
  unfold height
  rw [← centre_factor]
  by_cases he : f = centre c
  · subst f
    simp [order]
  · have hn : f.val ≠ (centre c).val := fun hh => he (Subtype.ext hh)
    simp [order,HorizontalOrders.valuation_factor_of_ne _ _ he,hn]

theorem centre_retained (c : Bool) : HorizontalOrders.Retained (poles (driver a).requirements) (centre c) := by
  let C := chain (driver a).requirements
  apply (HorizontalOrders.retained_range_iff C.raw (fun i => ⟨C.raw_monic i,C.raw_irreducible i⟩) _).mpr
  rintro ⟨n,h⟩
  have hdeg := C.raw_degree_five n
  rw [h,centre_factor] at hdeg
  change 5 ≤ (X - Polynomial.C ((if c then 1 else 0 : ℕ) : ℚ)).natDegree at hdeg
  rw [natDegree_X_sub_C] at hdeg
  omega

theorem centre_order_generator (c : Bool) (i : ℕ) :
    order (HorizontalOrders.valuation (centre c)) (generatorUnit (driver a) i).val = 0 := by
  apply (order_eq_zero_iff _ (generatorUnit (driver a) i).ne_zero).mpr
  apply AtomProfiles.generators_horizontal_valuation _ _ _ _ (centre_retained a c)
  exact fun j => ((chain (driver a).requirements).raw_monic j).ne_zero

theorem aux_prime_injective (k : Bool) : Function.Injective (fun j : Aux a k => j.prime) := by
  rintro ⟨p,i,e,h⟩ ⟨q,j,d,h'⟩ hp
  change p = q at hp
  subst q
  rw [h] at h'
  cases h'
  rfl

private theorem reg_inj (c k : Bool) : Function.Injective (fun i : ℕ => regularPrime a (c,k,i)) :=
  fun _ _ h => congrArg (fun l : RegularLabel => l.2.2) (regularPrime_injective a h)

theorem frozen_order {f : Horizontal} {t : ℕ} (hf : f.val ∈ ((driver a).actualRequest t).freeze)
    (p : PrimeIndex) (hp : p ∉ (driver a).assigned (max (t+1) (BulkInputs.scalarBound f))) (r : FibreRole)
    (hr : (driver a).permanentRole p = some r) :
    order (primaryVal a p (by rw [hr]; rfl)) (horizontalUnit f).val = Calibration.forecastOrder (height f.val) (some r) := by
  have h := ((driver a).frozen_rational_orders_outside t f hf (predicts a f) p hp r hr).1
  rw [primaryVal,evaluation_order]
  change (EvaluationDVR.evaluationHom _ _ _ (algebraMap ℚ[X] (RatFunc ℚ) f.val)).valuation = _
  rw [RawEvaluationPromises.evaluationHom_polynomial]
  exact h

theorem frozen_regular {f : Horizontal} {t : ℕ} (hf : f.val ∈ ((driver a).actualRequest t).freeze) (c k : Bool) :
    (Function.support (regDev a c k (horizontalUnit f))).Finite := by
  let S := (driver a).assigned (max (t+1) (BulkInputs.scalarBound f))
  apply (S.finite_toSet.preimage (reg_inj a c k).injOn).subset
  intro i hi
  by_contra hn
  have hz := frozen_order a hf _ hn _ (regularPrime_role a (c,k,i))
  apply hi
  change order (regularVal a (c,k,i)) (horizontalUnit f).val - _ = 0
  rw [show order (regularVal a (c,k,i)) (horizontalUnit f).val = height f.val c from hz,centre_order_horizontal]
  omega

theorem frozen_aux {f : Horizontal} {t : ℕ} (hf : f.val ∈ ((driver a).actualRequest t).freeze) (k : Bool) :
    (Function.support (auxOrder a k (horizontalUnit f))).Finite := by
  let S := (driver a).assigned (max (t+1) (BulkInputs.scalarBound f))
  apply (S.finite_toSet.preimage (aux_prime_injective a k).injOn).subset
  intro j hj
  by_contra hn
  exact hj (frozen_order a hf _ hn _ j.role_eq)

/-- The conditional stage formula suffices already to bound the support
of each normalized generator, also at primes that will be born later. -/
theorem generator_nonzero_row {n : ℕ} (p : PrimeIndex) (r : FibreRole) (hr : (driver a).permanentRole p = some r)
    (hn : order (primaryVal a p (by rw [hr]; rfl)) (generatorUnit (driver a) n).val ≠ 0) :
    ((driver a).actualRequest n).column.atPrimary p (some r) ≠ 0 := by
  let D := driver a
  obtain ⟨b,hb,he⟩ := (D.permanentRole_iff p r).mp hr
  have pair := ((D.actualRequest b).paired p hb).mpr (by rw [he]; rfl)
  have hv := D.generator_primary_order n b p hb pair
  rw [primaryVal,evaluation_order] at hn
  change ((permanentSite D.requirements p).evaluate false _ ((chain D.requirements).generators n)).valuation ≠ 0 at hn
  rw [hv,he] at hn
  split at hn
  · contradiction
  · exact hn

theorem generator_regular (n : ℕ) (c k : Bool) :
    (Function.support (regDev a c k (generatorUnit (driver a) n))).Finite := by
  let C := ((driver a).actualRequest n).column
  apply ((C.regularSupport.image (fun l => l.2.2)).finite_toSet).subset
  intro i hi
  have h : order (regularVal a (c,k,i)) (generatorUnit (driver a) n).val ≠ 0 := by
    simpa [Function.mem_support,regDev,centre_order_generator] using hi
  exact Finset.mem_image.mpr ⟨(c,k,i),C.supports_nonzero _ _ (generator_nonzero_row a _ _ (regularPrime_role a _) h),rfl⟩

theorem generator_aux (n : ℕ) (k : Bool) :
    (Function.support (auxOrder a k (generatorUnit (driver a) n))).Finite := by
  let C := ((driver a).actualRequest n).column
  let S : Finset PrimeIndex := match C with | .auxiliary q _ _ _ => {q} | _ => ∅
  apply (S.finite_toSet.preimage (aux_prime_injective a k).injOn).subset
  intro j hj
  have nz := generator_nonzero_row a _ _ j.role_eq hj
  change C.atPrimary j.prime (some (.auxiliary k j.index j.positive)) ≠ 0 at nz
  change j.prime ∈ S
  cases hC : C <;> simp_all [S,RawColumn.atPrimary]

end UnconditionalCounterexample.Variations.DyadicLedger.Calibrated
