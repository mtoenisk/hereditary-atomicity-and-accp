import UnconditionalCounterexample.Variations.MultiDomainLowHorizontal
import UnconditionalCounterexample.DiscreteOrders

/-!
# The complete system of coordinates for the ordinary multivariate domain

The retained horizontal prime classes are split at the first variable. The
resulting valuation family cuts out the actual ordinary domain and tests
divisibility there. All horizontal coordinates outside the first variable
have finite support.
-/

noncomputable section
namespace UnconditionalCounterexample.Variations.MultiDomain

open GuardSupport DiscreteOrders WithZero

variable {r : ℕ} (A : Data (r+1))

abbrev TPoly (r : ℕ) : Polys (r+1) := MvPolynomial.X 0
abbrev OtherPrime := {p : RetainedPrime A // p.val ≠ Associates.mk (TPoly r)}
abbrev Outside := PrimeIndex ⊕ OtherPrime A

def coordinateVal : ProfilePlace (Outside A) → Valuation (FunctionField (r+1)) ℤᵐ⁰
  | .limit => PrimeOrders.valuation (p := TPoly r) MvPolynomial.X_prime
  | .primary j => A.primary j
  | .outside (.inl p) => A.guard p
  | .outside (.inr p) => p.val.valAt

private theorem all_retained {x : FunctionField (r+1)} {P : ℤᵐ⁰ → Prop}
    (ht : P (coordinateVal A .limit x))
    (ho : ∀ p : OtherPrime A, P (coordinateVal A (.outside (.inr p)) x))
    {f : Polys (r+1)} (hf : Prime f) (hr : ∀ i, ¬ f ∣ A.raw i) :
    P (PrimeOrders.valuation hf x) := by
  by_cases h : Associates.mk f = Associates.mk (TPoly r)
  · rw [associated_valuation hf MvPolynomial.X_prime (Associates.mk_eq_mk_iff_associated.mp h)]
    exact ht
  · let p : RetainedPrime A := ⟨Associates.mk f, Associates.prime_mk.mpr hf,
      fun i hd ↦ hr i (Associates.mk_dvd_mk.mp hd)⟩
    have ha : Associated p.representative f :=
      Associates.mk_eq_mk_iff_associated.mp (Associates.quot_out p.val)
    rw [associated_valuation hf p.prime ha.symm]
    exact ho ⟨p,h⟩

theorem ordinary_eq_full (hX : ∀ i, ¬ TPoly r ∣ A.raw i) :
    ordinary A = fullIntersection (coordinateVal A) := by
  ext x
  rw [mem_ordinary, fullIntersection, IntersectionDomain.mem_intersection]
  simp only [Subring.mem_top, true_and]
  constructor
  · rintro ⟨hx, hpri, hguard⟩ p
    cases p with
    | limit => exact retained_integral A MvPolynomial.X_prime hX ⟨x,hx⟩
    | primary j => exact hpri j
    | outside i =>
      rcases i with p | p
      · exact hguard p
      · exact retained_integral A p.val.prime p.val.retained ⟨x,hx⟩
  · intro h
    exact ⟨(mem_pole_iff_retained A x).mpr (fun _ hp hr ↦
      all_retained A (P := (· ≤ 1)) (h .limit) (fun p ↦ h (.outside (.inr p))) hp hr),
      fun j ↦ h (.primary j), fun p ↦ h (.outside (.inl p))⟩

theorem coordinate_integral (hX : ∀ i, ¬ TPoly r ∣ A.raw i) (x : ordinary A) (p) :
    coordinateVal A p (x : FunctionField (r+1)) ≤ 1 :=
  DiscreteOrders.integral (coordinateVal A) ⟨(x : FunctionField (r+1)), by
    rw [← ordinary_eq_full A hX]; exact x.property⟩ p

theorem coordinate_dvd (hX : ∀ i, ¬ TPoly r ∣ A.raw i) (x y : ordinary A)
    (hx : x ≠ 0) (hy : y ≠ 0) :
    x ∣ y ↔ ∀ p, natOrder (coordinateVal A p) (x : FunctionField (r+1)) ≤
      natOrder (coordinateVal A p) (y : FunctionField (r+1)) := by
  revert x y
  rw [ordinary_eq_full A hX]
  exact fun _ _ hx hy ↦ dvd_iff_natOrder_le _ hx hy

theorem pole_unit_of_horizontal_zero {x : FunctionField (r+1)} (hx : x ≠ 0)
    (ht : order (coordinateVal A .limit) x = 0)
    (ho : ∀ p : OtherPrime A, order (coordinateVal A (.outside (.inr p))) x = 0) :
    ∃ u : (poleAlgebra A)ˣ, ((u : poleAlgebra A) : FunctionField (r+1)) = x := by
  have h (f : Polys (r+1)) (hp : Prime f) (hr : ∀ i, ¬f ∣ A.raw i) :
      PrimeOrders.valuation hp x = 1 :=
    all_retained A (P := (· = 1)) ((order_eq_zero_iff _ hx).mp ht)
      (fun p ↦ (order_eq_zero_iff _ hx).mp (ho p)) hp hr
  let z : poleAlgebra A := ⟨x, (mem_pole_iff_retained A x).mpr (fun f p r ↦ (h f p r).le)⟩
  let y : poleAlgebra A := ⟨x⁻¹, (mem_pole_iff_retained A _).mpr (fun f p r ↦ by simp [h f p r])⟩
  exact ⟨⟨z, y, Subtype.ext (mul_inv_cancel₀ hx), Subtype.ext (inv_mul_cancel₀ hx)⟩, rfl⟩

theorem finite_outside {x : FunctionField (r+1)} (hx : x ≠ 0)
    (hg : {p | A.guard p x ≠ 1}.Finite) :
    {i | order (coordinateVal A (.outside i)) x ≠ 0}.Finite := by
  have hh : {p : OtherPrime A | p.val.valAt x ≠ 1}.Finite :=
    (finite_horizontal_support A x hx).preimage Subtype.val_injective.injOn
  apply ((hg.image (Sum.inl (β := OtherPrime A))).union (hh.image (Sum.inr (α := PrimeIndex)))).subset
  rintro (p | p) h
  · exact Or.inl ⟨p, mt (order_eq_zero_iff _ hx).mpr h, rfl⟩
  · exact Or.inr ⟨p, mt (order_eq_zero_iff _ hx).mpr h, rfl⟩

theorem coordinate_other_first (p : OtherPrime A) :
    coordinateVal A (.outside (.inr p)) (coordinate 0) = 1 := by
  apply PrimeOrders.valuation_of_not_dvd
  intro hd
  apply p.property
  rw [← Associates.quot_out p.val.val]
  exact Associates.mk_eq_mk_iff_associated.mpr
    ((p.val.prime.irreducible.dvd_irreducible_iff_associated MvPolynomial.X_prime.irreducible).mp hd)

end UnconditionalCounterexample.Variations.MultiDomain
