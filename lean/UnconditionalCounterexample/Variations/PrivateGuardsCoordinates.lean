import UnconditionalCounterexample.Variations.PrivateGuardsDomain
import UnconditionalCounterexample.Variations.MultiDomainLowCoordinates

/-! # The full coordinate system for the punctured domain

The main polynomials and punctures share one horizontal localization. The two
places at each puncture prime give two additional outside coordinates.
-/

noncomputable section
namespace UnconditionalCounterexample.Variations.PrivateGuards.Live

open GuardSupport DiscreteOrders WithZero MultivariateSelection

variable {r d : ℕ} {M : ℕ → Type*} {c : Fin (r+1) → ℚ} (C : Config r d) (L : Rule r M c)
variable (primary : ℕ → Valuation (FunctionField (r+1)) ℤᵐ⁰)
  (guard : PrimeIndex → Valuation (FunctionField (r+1)) ℤᵐ⁰)

/-- Interleave both sets of inverted factors to reuse the retained horizontal valuations. -/
def mergedData : MultiDomain.Data (r+1) where
  raw := interleave (main C L) (puncture C L)
  raw_ne n := by unfold interleave; split
                 · exact (event C L _).irreducible.ne_zero
                 · exact (event C L _).irreducible_puncture.ne_zero
  primary := primary
  guard := guard

local notation "A" => mergedData C L primary guard

theorem merged_pole : MultiDomain.poleAlgebra A = horizontal C L := by
  have hm : MultiDomain.denominators A = inverted (Set.range (main C L)) (puncture C L) := by
    apply congrArg Submonoid.closure
    ext f
    constructor
    · rintro ⟨i,rfl⟩
      change interleave _ _ i ∈ _
      unfold interleave; split <;> first | exact Or.inl ⟨_,rfl⟩ | exact Or.inr ⟨_,rfl⟩
    · rintro (⟨i,rfl⟩ | ⟨i,rfl⟩)
      · exact ⟨2*i,interleave_even ..⟩
      · exact ⟨2*i+1,interleave_odd ..⟩
  unfold MultiDomain.poleAlgebra horizontal Family.poleAlgebra
  congr 1

abbrev Outside := MultiDomain.Outside A ⊕ (ℕ × Bool)

def coordinateVal : ProfilePlace (Outside C L primary guard) → Valuation (FunctionField (r+1)) ℤᵐ⁰
  | .limit => MultiDomain.coordinateVal A .limit
  | .primary j => primary j
  | .outside (.inl p) => MultiDomain.coordinateVal A (.outside p)
  | .outside (.inr p) => branchVal C L primary guard (.inr p)

local notation "V" => coordinateVal C L primary guard
local notation "D" => domain C L primary guard

private theorem mem_split (x : FunctionField (r+1)) : x ∈ D ↔ x ∈ MultiDomain.ordinary A ∧
    ∀ z : ℕ × Bool, branchVal C L primary guard (.inr z) x ≤ 1 := by
  rw [mem_domain,MultiDomain.mem_ordinary,merged_pole]
  constructor
  · rintro ⟨hh,hp,hg,ha,ho⟩
    exact ⟨⟨hh,hp,hg⟩,fun ⟨n,b⟩ => by cases b <;> first | exact ha n | exact ho n⟩
  · rintro ⟨⟨hh,hp,hg⟩,h⟩
    exact ⟨hh,hp,hg,fun n => h (n,false), fun n => h (n,true)⟩

variable (retained : ∀ i, ¬ MultiDomain.TPoly r ∣ (mergedData C L primary guard).raw i)

include retained in
theorem domain_eq_full : D = fullIntersection V := by
  ext x
  rw [mem_split,MultiDomain.ordinary_eq_full A retained]
  simp only [fullIntersection,IntersectionDomain.mem_intersection,Subring.mem_top,true_and]
  constructor
  · rintro ⟨h,hp⟩ p
    cases p with
    | limit => exact h .limit
    | primary j => exact h (.primary j)
    | outside i => cases i with
                   | inl i => exact h (.outside i)
                   | inr b => exact hp b
  · intro h
    exact ⟨fun p => by cases p with
                       | limit => exact h .limit
                       | primary j => exact h (.primary j)
                       | outside i => exact h (.outside (.inl i)),fun b => h (.outside (.inr b))⟩

include retained in
theorem coordinate_integral (x : D) (p) : V p (x : FunctionField (r+1)) ≤ 1 :=
  DiscreteOrders.integral V ⟨_,by rw [← domain_eq_full C L primary guard retained]; exact x.property⟩ p

include retained in
theorem coordinate_dvd (x y : D) (hx : x ≠ 0) (hy : y ≠ 0) :
    x ∣ y ↔ ∀ p, natOrder (V p) (x : FunctionField (r+1)) ≤ natOrder (V p) (y : FunctionField (r+1)) := by
  revert x y
  rw [domain_eq_full C L primary guard retained]
  exact fun _ _ hx hy => dvd_iff_natOrder_le _ hx hy

theorem finite_outside {x : FunctionField (r+1)} (hx : x ≠ 0) (hg : {p | guard p x ≠ 1}.Finite) :
    {i | order (V (.outside i)) x ≠ 0}.Finite := by
  apply Set.finite_preimage_inl_and_inr.mp
  refine ⟨MultiDomain.finite_outside A hx hg,?_⟩
  apply ((finite_support C L x hx).prod (Set.finite_univ : (Set.univ : Set Bool).Finite)).subset
  rintro ⟨n,b⟩ h
  refine ⟨?_,Set.mem_univ _⟩
  cases b
  · exact Or.inl (mt (order_eq_zero_iff _ hx).mpr h)
  · exact Or.inr (mt (order_eq_zero_iff _ hx).mpr h)

end UnconditionalCounterexample.Variations.PrivateGuards.Live
