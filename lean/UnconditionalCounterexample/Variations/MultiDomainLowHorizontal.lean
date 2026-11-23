import UnconditionalCounterexample.Variations.MultiDomainLowWords
import UnconditionalCounterexample.Variations.MultiDomainPrimeValuation
import Mathlib.RingTheory.Localization.NumDen
import Mathlib.RingTheory.UniqueFactorizationDomain.Finite

/-!
# The retained prime divisors of the horizontal localization

The reduced numerator and denominator of an arbitrary fraction test all
retained valuations at once. A negative order forces a retained prime factor
in the denominator. Only the finitely many prime classes dividing the two
polynomials can have nonzero order.
-/

noncomputable section
namespace UnconditionalCounterexample.Variations.MultiDomain

open WithZero IsFractionRing

variable {r : ℕ} (A : Data r)

theorem retained_integral {p : Polys r} (hp : Prime p) (hpr : ∀ i, ¬p ∣ A.raw i)
    (x : poleAlgebra A) : PrimeOrders.valuation hp (x : FunctionField r) ≤ 1 := by
  obtain ⟨⟨f, d⟩, hd⟩ := IsLocalization.surj (denominators A) x
  have hvd : ¬p ∣ (d : Polys r) := fun h ↦ by
    obtain ⟨i, hi⟩ := (prime_dvd_denominator_iff A hp).mp ⟨d, d.property, h⟩
    exact hpr i hi
  let v := PrimeOrders.valuation hp
  have he : (x : FunctionField r) * algebraMap (Polys r) (FunctionField r) d =
      algebraMap (Polys r) (FunctionField r) f := congrArg (poleAlgebra A).subtype hd
  have hv := congrArg v he
  rw [map_mul, show v (algebraMap (Polys r) _ d) = 1 from PrimeOrders.valuation_of_not_dvd hp hvd,
    mul_one] at hv
  rw [show PrimeOrders.valuation hp (x : FunctionField r) = _ from hv]
  by_cases hf : f = 0
  · simp [hf]
  · exact (PrimeOrders.valuation_of_polynomial hp hf).trans_le
      (exp_le_one_iff.mpr (neg_nonpos.mpr (Int.natCast_nonneg _)))

private theorem unit_of_all_prime_factors_inverted (d : Polys r) (hd : d ≠ 0)
    (hf : ∀ p : Polys r, Prime p → p ∣ d → ∃ i, p ∣ A.raw i) :
    IsUnit (algebraMap (Polys r) (poleAlgebra A) d) := by
  induction d using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => exact (hd rfl).elim
  | h₂ d hunit => exact hunit.map _
  | h₃ a p ha hp ih =>
    obtain ⟨i, hi⟩ := hf p hp (dvd_mul_right _ _)
    rw [map_mul]
    exact (isUnit_of_dvd_unit (map_dvd _ hi) (IsLocalization.map_units (poleAlgebra A)
      (⟨A.raw i, Submonoid.subset_closure (Set.mem_range_self i)⟩ : denominators A))).mul
        (ih ha (fun s hs hsa ↦ hf s hs (hsa.trans (dvd_mul_left _ _))))

/-- Simultaneous membership, including zero, without a fixed ordering of the
irreducible raw polynomials. -/
theorem mem_pole_iff_retained (x : FunctionField r) :
    x ∈ poleAlgebra A ↔ ∀ (p : Polys r) (hp : Prime p), (∀ i, ¬p ∣ A.raw i) →
      PrimeOrders.valuation hp x ≤ 1 := by
  classical
  refine ⟨fun hx p hp h ↦ retained_integral A hp h ⟨x,hx⟩, ?_⟩
  intro hx
  by_cases hzero : x = 0
  · simp [hzero]
  let R := Polys r
  let K := FunctionField r
  let f := num R x
  let d := den R x
  have hdn : (d : R) ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp d.property
  have hun : IsUnit (algebraMap R (poleAlgebra A) d) := by
    apply unit_of_all_prime_factors_inverted A d hdn
    intro p hp hpd
    by_contra! hret
    have hpn : ¬ p ∣ f := fun hpf ↦ hp.not_isUnit (num_den_reduced R x hpf hpd)
    have hval := hx p hp hret
    rw [← mk'_num_den' R x, map_div₀, PrimeOrders.valuation_of_not_dvd hp hpn,
      PrimeOrders.valuation_of_polynomial hp hdn, one_div, ← exp_neg, neg_neg, exp_le_one_iff] at hval
    have hpos := multiplicity_pos_of_dvd hpd (FiniteMultiplicity.of_prime_left hp hdn)
    omega
  let u := hun.unit
  have hcoe : ((u : poleAlgebra A) : K) = algebraMap R K d :=
    congrArg (poleAlgebra A).subtype hun.unit_spec
  have hi : (((u⁻¹ : (poleAlgebra A)ˣ) : poleAlgebra A) : K) = (algebraMap R K d)⁻¹ :=
    eq_inv_of_mul_eq_one_left (hcoe ▸ congrArg (poleAlgebra A).subtype u.inv_mul)
  rw [← mk'_num_den' R x, div_eq_mul_inv, ← hi]
  exact (poleAlgebra A).mul_mem ((poleAlgebra A).algebraMap_mem _) ((u⁻¹ : (poleAlgebra A)ˣ) : poleAlgebra A).property

/-- The prime order depends only on the associate class of the polynomial. -/
theorem associated_valuation {p s : Polys r} (hp : Prime p) (hs : Prime s)
    (hps : Associated p s) (x : FunctionField r) :
    PrimeOrders.valuation hp x = PrimeOrders.valuation hs x := by
  by_cases hx : x = 0
  · simp [hx]
  rw [← mk'_num_den' (Polys r) x, map_div₀, map_div₀]
  have hn : num (Polys r) x ≠ 0 := (num_eq_zero _).not.mpr hx
  have hd : (den (Polys r) x : Polys r) ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp (den (Polys r) x).property
  simp only [PrimeOrders.valuation_of_polynomial _ hn, PrimeOrders.valuation_of_polynomial _ hd,
    multiplicity_eq_of_associated_left hps]

abbrev RetainedPrime := {s : Associates (Polys r) // Prime s ∧ ∀ i, ¬s ∣ Associates.mk (A.raw i)}

namespace RetainedPrime
variable {A}

def representative (p : RetainedPrime A) : Polys r := Quot.out p.val

theorem prime (p : RetainedPrime A) : Prime p.representative :=
  Associates.prime_mk.mp ((Associates.quot_out p.val).symm ▸ p.property.1)

theorem retained (p : RetainedPrime A) (i : ℕ) : ¬ p.representative ∣ A.raw i := by
  intro h
  exact p.property.2 i ((Associates.quot_out p.val) ▸ Associates.mk_dvd_mk.mpr h)

def valAt (p : RetainedPrime A) : Valuation (FunctionField r) ℤᵐ⁰ := PrimeOrders.valuation p.prime

end RetainedPrime

theorem finite_horizontal_support (x : FunctionField r) (hx : x ≠ 0) :
    {p : RetainedPrime A | p.valAt x ≠ 1}.Finite := by
  classical
  let R := Polys r
  let f := num R x
  let d := (den R x : R)
  have hn : f ≠ 0 := (num_eq_zero _).not.mpr hx
  have hd : d ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp (den R x).property
  let S : Set (Associates R) := {s | s ∣ Associates.mk (f*d)}
  let : Fintype S := UniqueFactorizationMonoid.fintypeSubtypeDvd (Associates.mk (f*d))
    (Associates.mk_ne_zero.mpr (mul_ne_zero hn hd))
  have hf : S.Finite := Set.toFinite S
  apply (hf.preimage Subtype.val_injective.injOn).subset
  intro p hp
  change RetainedPrime A at p
  change p.val ∣ Associates.mk (f*d)
  by_contra h
  have hnd : ¬p.representative ∣ f*d := fun he ↦ h ((Associates.quot_out p.val) ▸ Associates.mk_dvd_mk.mpr he)
  have h₁ := PrimeOrders.valuation_of_not_dvd p.prime (fun he ↦ hnd (he.trans (dvd_mul_right _ _)))
  have h₂ := PrimeOrders.valuation_of_not_dvd p.prime (fun he ↦ hnd (he.trans (dvd_mul_left _ _)))
  apply hp
  change PrimeOrders.valuation p.prime x = 1
  rw [← mk'_num_den' R x, map_div₀, h₁, h₂, div_one]

end UnconditionalCounterexample.Variations.MultiDomain
