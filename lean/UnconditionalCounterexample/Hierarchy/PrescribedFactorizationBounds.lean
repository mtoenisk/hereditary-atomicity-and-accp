import UnconditionalCounterexample.Hierarchy.PrescribedPoleProfile
import UnconditionalCounterexample.Hierarchy.PrescribedBound
import UnconditionalCounterexample.Hierarchy.PrescribedTransfer
import UnconditionalCounterexample.IntersectionSpectrum
import Factorization.BFInstances

/-!
# Factorization bounds in the prescribed-length rings

A positive integer dominating all vertical orders of a given element is
divisible in the intersection by each of its factors with unit image in the
pole algebra. This supplies the divisibility hypothesis for ACCP descent.
-/

noncomputable section
namespace UnconditionalCounterexample.Hierarchy.Prescribed

open DiscreteOrders GuardSupport Factorization WithZero

local instance : Algebra ℚ (RatFunc ℚ) := RatFunc.instAlgebraOfPolynomial ℚ ℚ

variable {m : ℕ → ℕ} {p : PrimeIndex} {S : Set (Polynomial ℚ)}

private theorem ringSubtype_injective : Function.Injective (ringSubtype m p S) :=
  fun _ _ h => Subtype.ext (congrArg (fun z : PoleAlgebra.generated S => (z : RatFunc ℚ)) h)

/-- A positive integer dominating all the orders of `x` is a common multiple
of the divisors of `x` that are units in the pole algebra. -/
theorem dominatingInteger_dominatesUnitDivisors {x : ring m p S} (hx : x ≠ 0)
    {N : ℕ} (hN : 0 < N)
    (hr : ∀ t, order (rowVal m p t) (x : RatFunc ℚ) ≤ order (rowVal m p t) (N : RatFunc ℚ))
    (hg : ∀ q, q ≠ p → order (guardVal q) (x : RatFunc ℚ) ≤ order (guardVal q) (N : RatFunc ℚ)) :
    IsUnit (ringSubtype m p S (N : ring m p S)) ∧ ∀ v : ring m p S, v ∣ x →
      IsUnit (ringSubtype m p S v) → v ∣ (N : ring m p S) := by
  classical
  have hNK : (N : RatFunc ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  constructor
  · have hq : IsUnit (N : ℚ) := isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr hN.ne')
    simpa using hq.map (algebraMap ℚ (PoleAlgebra.generated S))
  · rintro v ⟨w, hw⟩ hv
    obtain ⟨b, hb⟩ := hv.exists_right_inv
    have hinv : (v : RatFunc ℚ) * (b : RatFunc ℚ) = 1 := congrArg Subtype.val hb
    have hvK : (v : RatFunc ℚ) ≠ 0 := left_ne_zero_of_mul_eq_one hinv
    have hxe : (x : RatFunc ℚ) = (v : RatFunc ℚ) * (w : RatFunc ℚ) := congrArg Subtype.val hw
    have hwK : (w : RatFunc ℚ) ≠ 0 := fun h => hx (Subtype.ext (by simpa [h] using hxe))
    have hbmem : (N : RatFunc ℚ) / v ∈ PoleAlgebra.generated S := by
      rw [div_eq_mul_inv, ← eq_inv_of_mul_eq_one_right hinv]
      exact (PoleAlgebra.generated S).mul_mem ((PoleAlgebra.generated S).natCast_mem N) b.property
    have integral (V : Valuation (RatFunc ℚ) ℤᵐ⁰)
        (hNbound : order V (x : RatFunc ℚ) ≤ order V (N : RatFunc ℚ)) (hwint : V (w : RatFunc ℚ) ≤ 1) :
        V ((N : RatFunc ℚ) / v) ≤ 1 := by
      rw [← order_nonneg_iff V (div_ne_zero hNK hvK), order_div V hNK hvK]
      rw [hxe, order_mul V hvK hwK] at hNbound
      have := (order_nonneg_iff V hwK).mpr hwint
      omega
    have hwmem := ((mem_ring_iff ..).mp w.property).2
    have hdiv : (N : RatFunc ℚ) / v ∈ ring m p S :=
      (mem_ring_iff ..).mpr ⟨hbmem, fun t => integral _ (hr t) (hwmem.1 t),
        fun q hq => integral _ (hg q hq) (hwmem.2 q hq)⟩
    refine ⟨⟨_,hdiv⟩, Subtype.ext ?_⟩
    change (N : RatFunc ℚ) = (v : RatFunc ℚ) * ((N : RatFunc ℚ) / v)
    field_simp

namespace Generators

variable (G : Generators m p)

theorem poleAlgebra_isBFDomain : IsBFDomain (PoleAlgebra.generated G.poles) := by
  let : IsPrincipalIdealRing (PoleAlgebra.generated G.poles) :=
    IntersectionSpectrum.poleAlgebra_isPrincipalIdealRing G.poles (by
      rintro _ ⟨i,rfl⟩
      exact (G.irreducible i).ne_zero)
  exact isBFDomain_of_uniqueFactorizationMonoid _

/-- Actual evaluation orders and the sum of all off-prime guard orders. -/
noncomputable def profileOrders : ProfileOrders m (ringSubtype m p G.poles) where
  row a x := natOrder (rowVal m p x) a.val
  guards a := guardMass p a.val
  row_mul a b ha hb x := natOrder_mul _ (fun h => ha (Subtype.ext h)) (fun h => hb (Subtype.ext h))
    (((mem_ring_iff ..).mp a.property).2.1 x) (((mem_ring_iff ..).mp b.property).2.1 x)
  guards_mul _ _ ha hb := guardMass_mul m p G.poles ha hb
  profile := G.natProfile_exists
  unit_of_zero a hu hg hr := by
    have ha : (a : RatFunc ℚ) ≠ 0 := fun h => hu.ne_zero (Subtype.ext h)
    have hint := ((mem_ring_iff ..).mp a.property).2
    apply G.unit_of_orders_zero a hu
    · intro x
      rw [← natOrder_cast _ ha (hint.1 x), hr]; rfl
    · intro q hq
      rw [← natOrder_cast _ ha (hint.2 q hq), guardNatOrder_zero_of_guardMass_eq_zero p _ hg q hq]
      rfl

/-- ACCP for the prescribed-length domain, including unbounded row sizes. -/
theorem domain_accp : WfDvdMonoid G.domain := by
  apply G.profileOrders.wfDvdMonoid ringSubtype_injective G.poleAlgebra_isBFDomain.wfDvdMonoid
  intro x hx
  obtain ⟨N, hN, hr, hg⟩ := exists_integer_dominating m p (x : RatFunc ℚ) (fun h => hx (Subtype.ext h))
  exact ⟨(N : G.domain), dominatingInteger_dominatesUnitDivisors hx hN hr hg⟩

/-- Two entries in every row give bounded factorization in the intersection. -/
theorem binary_domain_bf (H : Generators (fun _ => 0) p) : IsBFDomain H.domain :=
  H.profileOrders.isBFDomain ringSubtype_injective H.poleAlgebra_isBFDomain

end Generators
end UnconditionalCounterexample.Hierarchy.Prescribed
