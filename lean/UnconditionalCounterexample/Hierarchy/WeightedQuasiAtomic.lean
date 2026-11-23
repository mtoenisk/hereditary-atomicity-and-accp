import Factorization.BFInstances
import Factorization.StrictHierarchy
import UnconditionalCounterexample.DiscreteOrders
import UnconditionalCounterexample.PoleAlgebra
import Mathlib.Data.Nat.Factorization.Induction
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.PrincipalIdealDomain

/-!
# Atomic multiples from doubled vertical profiles

For a pole algebra B and vertical valuations, the actual intersection R
contains an atomic multiple of every nonzero element provided its vertical
profile can be doubled by a B-unit, integer clearing holds, and rational
primes are atoms. The pole factor bound follows from the PID structure
of the localization of ℚ[t].
-/

namespace UnconditionalCounterexample.Hierarchy.Weighted

open IntersectionDomain Factorization WithZero

theorem poleAlgebra_isBFDomain (S : Set (Polynomial ℚ)) (hS : ∀ f ∈ S, f ≠ 0) :
    IsBFDomain (PoleAlgebra.generated S) := by
  let B := PoleAlgebra.generated S
  let : IsLocalization (Submonoid.closure S) B := PoleAlgebra.isLocalization_generated S hS
  let : IsPrincipalIdealRing B := ⟨fun J => by
    rw [← IsLocalization.map_under (Submonoid.closure S) (B : Type) J]
    exact Submodule.IsPrincipal.map_ringHom _ (inferInstance : (J.under (Polynomial ℚ)).IsPrincipal)⟩
  exact isBFDomain_of_uniqueFactorizationMonoid B

variable {K ι : Type*} [Field K] (B : Subring K) (v : ι → Valuation K ℤᵐ⁰)

private theorem isUnit_of_pole_unit {a : intersection B v}
    (hunit : IsUnit (inclusion B v a)) (hv : ∀ i, v i (a : K) = 1) : IsUnit a := by
  obtain ⟨y, hy⟩ := hunit.exists_right_inv
  have he : (a : K) * (y : K) = 1 := congrArg Subtype.val hy
  have hval (i : ι) : v i (y : K) = 1 := by
    simpa only [map_mul, hv i, one_mul, map_one] using congrArg (v i) he
  let b : intersection B v := ⟨y, (mem_intersection _ _ _).mpr ⟨y.property, fun i => (hval i).le⟩⟩
  exact isUnit_iff_exists_inv.mpr ⟨b, Subtype.ext he⟩

/-- With all vertical orders zero, every nonunit divisor remains a nonunit
in the pole algebra. The pole-algebra length bound gives atomicity in R. -/
theorem atomic_of_vertical_units (hB : IsBFDomain B) (z : intersection B v)
    (hz : z ≠ 0) (hv : ∀ i, v i (z : K) = 1) : HasAtomicFactorization z := by
  let f := (inclusion B v).toMonoidHom
  have hzB : f z ≠ 0 := fun h => hz (Subtype.ext (congrArg (fun b : B => b.val) h))
  obtain ⟨n, hn⟩ := hB (f z) hzB
  apply HasBoundedFactorizations.hasAtomicFactorization
  refine ⟨n, fun s hs hprod => ?_⟩
  have hnon : ∀ q ∈ s.map f, ¬ IsUnit q := by
    intro q hq hu
    obtain ⟨a, ha, rfl⟩ := Multiset.mem_map.mp hq
    apply hs a ha
    apply isUnit_of_pole_unit B v hu
    obtain ⟨y, hy⟩ := (Multiset.dvd_prod ha).trans hprod.dvd
    intro i
    have hia := ((mem_intersection B v _).mp a.property).2 i
    have hiy := ((mem_intersection B v _).mp y.property).2 i
    have he := hv i
    rw [hy, Subring.coe_mul, map_mul] at he
    exact le_antisymm hia (he ▸ (mul_le_of_le_one_right' hiy))
  have hassoc : Associated (s.map f).prod (f z) := by
    rw [← map_multiset_prod]
    exact hprod.map f
  simpa only [Multiset.card_map] using hn (s.map f) hnon hassoc

private theorem integer_atomic {R : Type*} [CommRing R] [IsDomain R]
    (hp : ∀ p : ℕ, p.Prime → Irreducible (p : R)) (n : ℕ) (hn : 0 < n) :
    HasAtomicFactorization (n : R) := by
  induction n using Nat.recOnMul with
  | zero => omega
  | one => simpa using hasAtomicFactorization_of_isUnit (isUnit_one : IsUnit (1:R))
  | prime p h => exact hasAtomicFactorization_of_irreducible (hp p h)
  | mul a b ha hb =>
    rw [Nat.cast_mul]
    exact (ha (Nat.pos_of_mul_pos_right hn)).mul (hb (Nat.pos_of_mul_pos_left hn))

/-- Quasi-atomicity for all nonzero elements of the actual intersection.
The two profile inputs respectively realize the doubled orders by a pole
unit and clear a field element into every vertical valuation ring. -/
theorem quasiAtomic_of_doubled_profiles [CharZero K] (hB : IsBFDomain B)
    (hdoubled : ∀ x : intersection B v, x ≠ 0 → ∃ u : Bˣ, ∀ i,
      v i ((u.val : B) : K) = v i (x : K) ^ 2)
    (hclear : ∀ f : K, f ≠ 0 → ∃ n : ℕ, 0 < n ∧ ∀ i, v i ((n : K) * f) ≤ 1)
    (hprime : ∀ p : ℕ, p.Prime → Irreducible (p : intersection B v)) :
    IsQuasiAtomicDomain (intersection B v) := by
  apply isQuasiAtomicDomain_iff_dvd_atomic.mpr
  intro x hx
  have hxK : (x : K) ≠ 0 := fun h => hx (Subtype.ext h)
  obtain ⟨u, hu⟩ := hdoubled x hx
  let w : K := ((u⁻¹).val : B)
  have hw : ((u.val : B) : K) * w = 1 :=
    congrArg Subtype.val u.val_inv
  have hw0 := right_ne_zero_of_mul (hw.trans_ne one_ne_zero)
  have hcx := intersection_le B v x.property
  have hwB : w ∈ B := (u⁻¹).val.property
  have hvz (i : ι) : v i ((x : K)^2 * w) = 1 := by
    rw [map_mul, map_pow, ← hu i, ← map_mul, hw, map_one]
  let z : intersection B v := ⟨(x : K)^2 * w, (mem_intersection _ _ _).mpr
    ⟨B.mul_mem (B.pow_mem hcx _) hwB, fun i => (hvz i).le⟩⟩
  have hz := atomic_of_vertical_units B v hB z
    (fun h => mul_ne_zero (pow_ne_zero _ hxK) hw0 (congrArg Subtype.val h)) hvz
  obtain ⟨n, hn, hnv⟩ := hclear ((x : K) * w) (mul_ne_zero hxK hw0)
  let y : intersection B v := ⟨(n : K) * ((x : K) * w), (mem_intersection _ _ _).mpr
    ⟨B.mul_mem (natCast_mem B _) (B.mul_mem hcx hwB), hnv⟩⟩
  refine ⟨n * z, (integer_atomic hprime n hn).mul hz, y, ?_⟩
  apply Subtype.ext
  change (n : K) * ((x : K)^2 * w) = (x : K) * ((n : K) * ((x : K) * w))
  ring

end UnconditionalCounterexample.Hierarchy.Weighted
