import Mathlib.NumberTheory.Padics.ValuativeRel
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.Tactic.Ring

/-!
# The extra rational point for the dimension r+1 construction

The value at the reserved point is rational. Requiring this value to be
q-integral preserves normality and the fraction field; reduction of this
value has strictly larger kernel than evaluation itself.
-/

noncomputable section

namespace UnconditionalCounterexample.Variations.PointPullback

theorem integrallyClosedIn_comap {R A : Type*} [CommRing R] [CommRing A] (ev : R →+* A)
    (W : Subring A) [IsIntegrallyClosedIn W A] : IsIntegrallyClosedIn (W.comap ev) R := by
  apply Subring.isIntegrallyClosedIn_iff.mpr
  intro x hx
  let φ : W.comap ev →+* W := (ev.comp (W.comap ev).subtype).codRestrict W (fun x => x.property)
  exact Subring.isIntegrallyClosedIn_iff.mp ‹IsIntegrallyClosedIn W A›
    (IsIntegral.map_of_comp_eq φ ev rfl hx)

/-- The rational numbers integral at the reserved prime. -/
def localRationals (q : ℕ) [Fact q.Prime] : Subring ℚ :=
  (PadicInt.subring q).comap (Rat.castHom ℚ_[q])

private theorem localRationals_closed (q : ℕ) [Fact q.Prime] :
    IsIntegrallyClosedIn (localRationals q) ℚ := by
  let : IsFractionRing (PadicInt.subring q) ℚ_[q] := inferInstanceAs (IsFractionRing ℤ_[q] ℚ_[q])
  have : IsIntegrallyClosedIn (PadicInt.subring q) ℚ_[q] :=
    (isIntegrallyClosed_iff_isIntegrallyClosedIn ℚ_[q]).mp
      (inferInstance : IsIntegrallyClosed ℤ_[q])
  exact integrallyClosedIn_comap _ _

/-- View the pullback as an actual subring of the original fraction field. -/
def domain {K : Type*} [Field K] (D : Subring K) (ev : D →+* ℚ) (q : ℕ) [Fact q.Prime] :
    Subring K := ((localRationals q).comap ev).map D.subtype

theorem normal {K : Type*} [Field K] (D : Subring K) [IsIntegrallyClosed D]
    (ev : D →+* ℚ) (q : ℕ) [Fact q.Prime] : IsIntegrallyClosed (domain D ev q) := by
  let W := localRationals q
  let := localRationals_closed q
  let := integrallyClosedIn_comap ev W
  let := IsIntegrallyClosed.of_isIntegrallyClosed_of_isIntegrallyClosedIn (R := W.comap ev) (S := D)
  exact IsIntegrallyClosed.of_equiv ((W.comap ev).equivMapOfInjective _ Subtype.val_injective)

private theorem clear {R : Type*} [CommRing R] (ev : R →+* ℚ) (W : Subring ℚ) (x : R) :
    ((ev x).den : R) * x ∈ W.comap ev := by
  change ev _ ∈ W
  rw [map_mul, map_natCast, mul_comm]
  have heq := (div_eq_iff (Nat.cast_ne_zero.mpr (ev x).den_nz : ((ev x).den : ℚ) ≠ 0)).mp
    (ev x).num_div_den
  exact heq ▸ intCast_mem W _

theorem fractionRing {K : Type*} [Field K] [CharZero K] (D : Subring K) [IsFractionRing D K]
    (ev : D →+* ℚ) (q : ℕ) [Fact q.Prime] : IsFractionRing (domain D ev q) K := by
  apply IsFractionRing.of_field
  intro z
  obtain ⟨x, y, _, hxy⟩ := IsFractionRing.div_surjective D z
  let W := (localRationals q).comap ev
  let d := (ev x).den * (ev y).den
  have hd : (d : K) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.mul_ne_zero (ev x).den_nz (ev y).den_nz)
  have hx : (d : D) * x ∈ W := by
    rw [show (d : D) * x = ((ev y).den : D) * (((ev x).den : D) * x) by simp [d]; ring]
    exact W.mul_mem (natCast_mem W _) (clear ev _ _)
  have hy : (d : D) * y ∈ W := by
    rw [show (d : D) * y = ((ev x).den : D) * (((ev y).den : D) * y) by simp [d, mul_assoc]]
    exact W.mul_mem (natCast_mem W _) (clear ev _ _)
  refine ⟨⟨_, ⟨_, hx, rfl⟩⟩, ⟨_, ⟨_, hy, rfl⟩⟩, ?_⟩
  change z = (d * (x : K)) / (d * (y : K))
  rw [mul_div_mul_left _ _ hd]
  exact hxy.symm

/-- Evaluate the actual embedded pullback at the reserved rational point. -/
def pointValue {K : Type*} [Field K] (D : Subring K) (ev : D →+* ℚ) (q : ℕ) [Fact q.Prime] :
    domain D ev q →+* localRationals q := by
  let A := (localRationals q).comap ev
  let f : A →+* localRationals q := (ev.comp A.subtype).codRestrict _ (fun x => x.property)
  exact f.comp (A.equivMapOfInjective _ Subtype.val_injective).symm.toRingHom

/-- Reduction modulo the reserved prime on the same domain. -/
def reduction (q : ℕ) [Fact q.Prime] : localRationals q →+* ZMod q :=
  PadicInt.toZMod.comp (((Rat.castHom ℚ_[q]).comp (localRationals q).subtype).codRestrict
    (PadicInt.subring q) (fun x => x.property))

theorem ker_pointValue_lt_ker_reduction {K : Type*} [Field K] (D : Subring K)
    (ev : D →+* ℚ) (q : ℕ) [Fact q.Prime] :
    RingHom.ker (pointValue D ev q) < RingHom.ker ((reduction q).comp (pointValue D ev q)) := by
  refine lt_of_le_of_ne (fun x hx => ?_) ?_
  · change reduction q (pointValue D ev q x) = 0
    rw [RingHom.mem_ker.mp hx, map_zero]
  · intro heq
    have hq : (q : domain D ev q) ∈ RingHom.ker ((reduction q).comp (pointValue D ev q)) := by
      rw [RingHom.mem_ker, map_natCast, ZMod.natCast_self]
    rw [← heq, RingHom.mem_ker, map_natCast] at hq
    have h0 : (q : ℚ) = 0 := congrArg Subtype.val hq
    exact (Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero) h0

end UnconditionalCounterexample.Variations.PointPullback
