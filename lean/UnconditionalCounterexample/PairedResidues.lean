import UnconditionalCounterexample.ReturnCongruences
import Mathlib.RingTheory.Ideal.Quotient.Operations


/-!
# Actual paired residue quotients

For the literal intersection domain attached to a pole algebra and paired
p-adic evaluations, evaluation followed by reduction modulo p^h gives a ring
map to `(ZMod (p^h))^2`. Its kernel is exactly p^h D: divide by p^h in the
rational pole algebra, use the two integral evaluation quotients above p, and
use that p is a unit at every other rational prime.

When the primary argument is a nonunit and the guard argument is a unit,
their difference is a unit. Integer constants and the actual coordinate t
then give surjectivity, hence the canonical prime-power quotient equivalence.
No maximal-spectrum theorem, finite-support estimate, approximation, or
abstract desired residue-map hypothesis is used.
-/

namespace UnconditionalCounterexample.PairedResidues
noncomputable section
open Polynomial GuardSupport WithZero

/-- A primary in the maximal ideal differs by a unit from a unit guard. -/
theorem difference_isUnit {p : ℕ} [Fact p.Prime] (α β : ℤ_[p])
    (hα : ¬ IsUnit α) (hβ : IsUnit β) : IsUnit (β - α) := by
  have hα0 : PadicInt.toZMod α = 0 := by
    by_contra h
    exact hα ((padicInt_isUnit_iff_toZMod_ne_zero α).mpr h)
  apply (padicInt_isUnit_iff_toZMod_ne_zero _).mpr
  rw [map_sub, hα0, sub_zero]
  exact (padicInt_isUnit_iff_toZMod_ne_zero _).mp hβ

/-- Positive additive valuation is the precise primary nonunit condition. -/
theorem not_isUnit_of_valuation_pos {p : ℕ} [Fact p.Prime] (α : ℤ_[p])
    (hα : 0 < (α : ℚ_[p]).valuation) : ¬ IsUnit α := by
  apply PadicInt.not_isUnit_iff.mpr
  change ‖(α : ℚ_[p])‖ < 1
  have hne : (α : ℚ_[p]) ≠ 0 := by
    intro h
    simp only [h, Padic.valuation_zero, lt_self_iff_false] at hα
  rw [Padic.norm_eq_zpow_neg_valuation hne]
  exact (zpow_lt_one_iff_right₀ (by exact_mod_cast (Fact.out : p.Prime).one_lt)).mpr
    (neg_neg_of_pos hα)

/-- Integer constants and one pair with unit coordinate difference make the
actual residue map surjective. -/
theorem pairMap_surjective_of_unit_difference {A : Type*} [CommRing A] (m : ℕ)
    (f : A →+* ZMod m × ZMod m) (t : A) (ht : IsUnit ((f t).2 - (f t).1)) :
    Function.Surjective f := by
  obtain ⟨u,hu⟩ := ht
  rintro ⟨x,y⟩
  let d : ZMod m := (y-x) * ↑u⁻¹
  let c : ZMod m := x-d*(f t).1
  obtain ⟨a,ha⟩ := ZMod.intCast_surjective c
  obtain ⟨b,hb⟩ := ZMod.intCast_surjective d
  refine ⟨(a:A)+(b:A)*t,?_⟩
  have hd : d*((f t).2-(f t).1) = y-x := by
    dsimp [d]
    rw [← hu, mul_assoc, Units.inv_mul, mul_one]
  rw [map_add, map_mul, map_intCast, map_intCast]
  apply Prod.ext
  · change (a:ZMod m)+(b:ZMod m)*(f t).1=x
    rw [ha,hb]
    dsimp [c]
    ring
  · change (a:ZMod m)+(b:ZMod m)*(f t).2=y
    rw [ha,hb]
    dsimp [c]
    calc
      x-d*(f t).1+d*(f t).2 = x+d*((f t).2-(f t).1) := by ring
      _ = y := by rw [hd]; ring

/-- A different rational prime has unit value under every evaluation at q. -/
theorem valuation_prime_eq_one_of_ne {K : Type*} [Field K]
    (p q : ℕ) [Fact p.Prime] [Fact q.Prime] (e : K →+* ℚ_[q]) (hpq : p ≠ q) :
    EvaluationDVR.valuation q e (p : K) = 1 := by
  have hnot : ¬ (q : ℤ) ∣ (p : ℤ) := by
    rw [Int.natCast_dvd_natCast]
    intro h
    have heq := (Nat.prime_dvd_prime_iff_eq (Fact.out : q.Prime) (Fact.out : p.Prime)).mp h
    exact hpq heq.symm
  have hv := congrArg (fun v : Valuation ℤ ℤᵐ⁰ => v (p : ℤ))
    (Padic.comap_mulValuation_eq_int_padicValuation (p := q))
  have hval : Padic.mulValuation (p : ℚ_[q]) = 1 := by
    have hpv := (Int.padicValuation_eq_one_iff (p := q) (x := (p : ℤ))).mpr hnot
    simpa only [Valuation.comap_apply, Int.coe_castRingHom, Int.cast_natCast] using hv.trans hpv
  simpa only [EvaluationDVR.valuation, Valuation.comap_apply, map_natCast] using hval

/-- Vanishing modulo p^h of an integral evaluation is exactly the local
integrality needed after division by p^h. -/
theorem valuation_div_pow_le_one_of_residue_zero {K : Type*} [Field K]
    (p : ℕ) [Fact p.Prime] (e : K →+* ℚ_[p]) (h : ℕ) (x : K) (z : ℤ_[p])
    (hz : e x = z) (hzero : PadicInt.toZModPow h z = 0) :
    EvaluationDVR.valuation p e (x / (p : K)^h) ≤ 1 := by
  have hm : z ∈ RingHom.ker (PadicInt.toZModPow h) := hzero
  rw [PadicInt.ker_toZModPow, Ideal.mem_span_singleton] at hm
  obtain ⟨w,hw⟩ := hm
  have hp : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have heq : e (x / (p : K)^h) = (w : ℚ_[p]) := by
    rw [map_div₀, map_pow, map_natCast, hz]
    have hw' := congrArg (fun z : ℤ_[p] => (z : ℚ_[p])) hw
    simp only [PadicInt.coe_mul, PadicInt.coe_pow, PadicInt.coe_natCast] at hw'
    rw [hw', mul_div_cancel_left₀ _ (pow_ne_zero _ hp)]
  exact (EvaluationDVR.mem_valuationSubring p e _).mpr (by rw [heq]; exact w.property)

open PairedDomain
local instance : Algebra ℚ (RatFunc ℚ) := RatFunc.instAlgebraOfPolynomial ℚ ℚ

variable (S : Set ℚ[X]) (d : Places)

def branchArgument (j : ℕ) (b : Bool) : ℤ_[(d.primes j).val] :=
  if b then d.guard (d.primes j) else d.primary j

/-- Literal evaluation of an element of the intersection in the p-adic integers. -/
def branchIntegerMap (j : ℕ) (b : Bool) : domain S d →+* ℤ_[(d.primes j).val] :=
  ((evaluationBranch d j b).comp (domain S d).subtype).codRestrict
    (PadicInt.subring (d.primes j).val)
    (fun x => ((mem_domain_iff_branches d S x).mp x.property).2 j b)

@[simp] theorem branchIntegerMap_coe (j : ℕ) (b : Bool) (x : domain S d) :
    (branchIntegerMap S d j b x : ℚ_[(d.primes j).val]) = evaluationBranch d j b x := rfl

@[simp] theorem branchIntegerMap_X (j : ℕ) (b : Bool) :
    branchIntegerMap S d j b ⟨RatFunc.X, X_mem S d⟩ = branchArgument d j b := by
  apply Subtype.ext
  change evaluationBranch d j b RatFunc.X = (branchArgument d j b : ℚ_[(d.primes j).val])
  cases b <;> simp [branchArgument, evaluationBranch, guardEvaluation]

/-- Primary and guard evaluation followed by reduction modulo p^h. -/
def pairResidue (j h : ℕ) : domain S d →+*
    ZMod ((d.primes j).val ^ h) × ZMod ((d.primes j).val ^ h) :=
  ((PadicInt.toZModPow h).comp (branchIntegerMap S d j false)).prod
    ((PadicInt.toZModPow h).comp (branchIntegerMap S d j true))

@[simp] theorem pairResidue_X (j h : ℕ) :
    pairResidue S d j h ⟨RatFunc.X, X_mem S d⟩ =
      (PadicInt.toZModPow h (d.primary j), PadicInt.toZModPow h (d.guard (d.primes j))) := by
  simp [pairResidue, branchArgument]

theorem pairResidue_eq_zero_iff (j h : ℕ) (x : domain S d) :
    pairResidue S d j h x = 0 ↔
      ∀ b : Bool, PadicInt.toZModPow h (branchIntegerMap S d j b x) = 0 := by
  change (_,_) = (0,0) ↔ _
  rw [Prod.mk.injEq]
  constructor
  · rintro ⟨hf,ht⟩ b
    cases b
    · exact hf
    · exact ht
  · intro h
    exact ⟨h false,h true⟩

/-- The defining intersection permits division by p^h exactly when the two
p-adic values above p vanish modulo p^h. -/
theorem div_pow_mem_domain_of_pairResidue_eq_zero (i h : ℕ) (x : domain S d)
    (hx : pairResidue S d i h x = 0) :
    (x : RatFunc ℚ) / ((d.primes i).val : RatFunc ℚ)^h ∈ domain S d := by
  apply (mem_domain_iff_branches d S _).mpr
  obtain ⟨hxB,hxb⟩ := (mem_domain_iff_branches d S _).mp x.property
  constructor
  · rw [div_eq_mul_inv]
    apply (PoleAlgebra.generated S).mul_mem hxB
    simpa using (PoleAlgebra.generated S).algebraMap_mem (((d.primes i).val : ℚ)^h)⁻¹
  · intro j b
    by_cases hji : j=i
    · subst j
      have hzero := (pairResidue_eq_zero_iff S d i h x).mp hx b
      have hv := valuation_div_pow_le_one_of_residue_zero (d.primes i).val
        (evaluationBranch d i b) h (x : RatFunc ℚ) (branchIntegerMap S d i b x) rfl hzero
      exact (EvaluationDVR.mem_valuationSubring _ _ _).mp hv
    · have hpq : (d.primes i).val ≠ (d.primes j).val := by
        intro heq
        exact hji (d.primes.injective (Subtype.ext heq)).symm
      have hunit := valuation_prime_eq_one_of_ne (d.primes i).val (d.primes j).val
        (evaluationBranch d j b) hpq
      apply (EvaluationDVR.mem_valuationSubring _ _ _).mp
      change EvaluationDVR.valuation _ _ (_ / _^h) ≤ 1
      rw [map_div₀, map_pow, hunit, one_pow, div_one]
      exact (EvaluationDVR.mem_valuationSubring _ _ _).mpr (hxb j b)

/-- The kernel is the actual principal ideal p^hD, without any difference-unit
or finite-support assumption. -/
theorem pairResidue_ker (i h : ℕ) :
    RingHom.ker (pairResidue S d i h) = Ideal.span {((d.primes i).val : domain S d)^h} := by
  apply le_antisymm
  · intro x hx
    have hx0 : pairResidue S d i h x = 0 := hx
    apply Ideal.mem_span_singleton.mpr
    refine ⟨⟨(x : RatFunc ℚ) / ((d.primes i).val : RatFunc ℚ)^h,
      div_pow_mem_domain_of_pairResidue_eq_zero S d i h x hx0⟩,?_⟩
    apply Subtype.ext
    change (x : RatFunc ℚ) = ((d.primes i).val : RatFunc ℚ)^h *
      ((x : RatFunc ℚ) / ((d.primes i).val : RatFunc ℚ)^h)
    exact (mul_div_cancel₀ _ (pow_ne_zero h
      (Nat.cast_ne_zero.mpr (d.primes i).property.ne_zero))).symm
  · apply Ideal.span_le.mpr
    rintro x rfl
    change pairResidue S d i h (((d.primes i).val : domain S d)^h) = 0
    rw [map_pow, map_natCast]
    apply Prod.ext <;> change ((d.primes i).val : ZMod ((d.primes i).val^h))^h = 0
    all_goals rw [← Nat.cast_pow, ZMod.natCast_self]

theorem pairResidue_ker_natCast (i h : ℕ) :
    RingHom.ker (pairResidue S d i h) =
      Ideal.span {(((d.primes i).val ^ h : ℕ) : domain S d)} := by
  simpa only [Nat.cast_pow] using pairResidue_ker S d i h

/-- The primary/guard coordinate difference is a unit at every finite precision. -/
theorem pairResidue_X_difference_isUnit (i h : ℕ)
    (hα : ¬ IsUnit (d.primary i)) (hβ : IsUnit (d.guard (d.primes i))) :
    IsUnit ((pairResidue S d i h ⟨RatFunc.X, X_mem S d⟩).2 -
      (pairResidue S d i h ⟨RatFunc.X, X_mem S d⟩).1) := by
  rw [pairResidue_X]
  simpa only [map_sub] using
    (difference_isUnit (d.primary i) (d.guard (d.primes i)) hα hβ).map
      (PadicInt.toZModPow h)

theorem pairResidue_surjective (i h : ℕ)
    (hα : ¬ IsUnit (d.primary i)) (hβ : IsUnit (d.guard (d.primes i))) :
    Function.Surjective (pairResidue S d i h) :=
  pairMap_surjective_of_unit_difference _ _ ⟨RatFunc.X, X_mem S d⟩
    (pairResidue_X_difference_isUnit S d i h hα hβ)

/-- The actual prime-power quotient of the intersection domain is the residue pair. -/
def primePowerQuotientEquiv (i h : ℕ)
    (hα : ¬ IsUnit (d.primary i)) (hβ : IsUnit (d.guard (d.primes i))) :
    (domain S d ⧸ Ideal.span {((d.primes i).val : domain S d)^h}) ≃+*
      ZMod ((d.primes i).val^h) × ZMod ((d.primes i).val^h) :=
  (Ideal.quotEquivOfEq (pairResidue_ker S d i h).symm).trans
    (RingHom.quotientKerEquivOfSurjective (pairResidue_surjective S d i h hα hβ))

@[simp] theorem primePowerQuotientEquiv_mk (i h : ℕ)
    (hα : ¬ IsUnit (d.primary i)) (hβ : IsUnit (d.guard (d.primes i))) (x : domain S d) :
    primePowerQuotientEquiv S d i h hα hβ
      (Ideal.Quotient.mk (Ideal.span {((d.primes i).val : domain S d)^h}) x) =
      pairResidue S d i h x := rfl

theorem primary_not_isUnit_of_pos (i : ℕ) (hi : 0 < i) : ¬ IsUnit (d.primary i) :=
  not_isUnit_of_valuation_pos _ (by rw [d.primary_late i hi]; decide)

/-- Only the first primary needs an additional nonunit hypothesis beyond Places. -/
theorem primary_not_isUnit (hfirst : ¬ IsUnit (d.primary 0)) (i : ℕ) :
    ¬ IsUnit (d.primary i) := by
  by_cases hi : i=0
  · subst i
    exact hfirst
  · exact primary_not_isUnit_of_pos d i (Nat.pos_of_ne_zero hi)

end
end UnconditionalCounterexample.PairedResidues
