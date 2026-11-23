import UnconditionalCounterexample.Variations.PrivateGuardsRealized
import UnconditionalCounterexample.Variations.MultiDomainDimension
import UnconditionalCounterexample.Variations.MultiDomainLowScalars
import UnconditionalCounterexample.RationalSigns

/-!
# The enlarged intersection for prescribed lower dimension

The horizontal ring inverts the main polynomials and the chosen punctures. The
vertical intersection uses the primary, public guard, private, and paired ordinary
valuations in their common rational function field.
-/

noncomputable section
namespace UnconditionalCounterexample.Variations.PrivateGuards.Live

open MvPolynomial GuardSupport MultivariateSelection IntersectionDomain WithZero
open scoped nonZeroDivisors

variable {r d : ℕ} {c : Fin (r+1) → ℚ} {M : ℕ → Type*} (C : Config r d) (L : Rule r M c)


abbrev Branch := (ℕ ⊕ PrimeIndex) ⊕ (ℕ × Bool)

abbrev horizontal := (family C L).poleAlgebra (fun n ↦ (event C L n).irreducible)

variable (primary : ℕ → Valuation (FunctionField (r+1)) ℤᵐ⁰) (guard : PrimeIndex → Valuation (FunctionField (r+1)) ℤᵐ⁰)

def branchVal : Branch → Valuation (FunctionField (r+1)) ℤᵐ⁰
  | .inl (.inl j) => primary j
  | .inl (.inr p) => guard p
  | .inr (n,false) => (family C L).places.auxiliary n
  | .inr (n,true) => (family C L).places.ordinary n

def domain : Subring (FunctionField (r+1)) := intersection (horizontal C L).toSubring (branchVal C L primary guard)

theorem mem_domain {z : (FunctionField (r+1))} : z ∈ domain C L primary guard ↔ z ∈ horizontal C L ∧
    (∀ j, primary j z ≤ 1) ∧ (∀ p, guard p z ≤ 1) ∧
    (∀ j, (family C L).places.auxiliary j z ≤ 1) ∧ ∀ j, (family C L).places.ordinary j z ≤ 1 := by
  rw [domain,mem_intersection]
  refine and_congr_right fun _ ↦ ⟨fun h ↦ ⟨fun j ↦ h (.inl (.inl j)), fun p ↦ h (.inl (.inr p)),
    fun n ↦ h (.inr (n,false)), fun n ↦ h (.inr (n,true))⟩,?_⟩
  rintro ⟨hp,hg,ha,ho⟩ ((i|v)|⟨j,b⟩)
  · exact hp i
  · exact hg v
  · cases b with
    | false => exact ha j
    | true => exact ho j

private theorem place_coordinate {p : PrimeIndex} (v : Fin (r+1) → ℤ_[p.val])
    (h : AlgebraicIndependent ℚ fun i ↦ (v i).val) (j : Fin (r+1)) :
    place p v h (MultiDomain.coordinate j) ≤ 1 := by
  rw [MultiDomain.coordinate,place_polynomial]
  change Padic.mulValuation (aeval (fun i ↦ (v i).val) (X j : Poly r)) ≤ 1
  rw [aeval_X]
  have hiff : ‖(v j).val‖ ≤ 1 ↔ Padic.mulValuation (v j).val ≤ 1 := by
    simpa only [not_lt, norm_one, map_one] using not_congr
      (Padic.norm_lt_norm_iff_mulValuation_lt (x := (1 : ℚ_[p.val])) (y := (v j).val))
  exact hiff.mp (v j).property

theorem domain_coordinate (hp : ∀ j i, primary j (MultiDomain.coordinate i) ≤ 1)
    (hg : ∀ p i, guard p (MultiDomain.coordinate i) ≤ 1) (i : Fin (r+1)) :
    MultiDomain.coordinate i ∈ domain C L primary guard := by
  apply (mem_domain C L primary guard).mpr
  exact ⟨(horizontal C L).algebraMap_mem _,fun j ↦ hp j i,fun p ↦ hg p i,
    fun n ↦ place_coordinate _ ((family C L).sites n).private_independent i,
    fun n ↦ place_coordinate _ ((family C L).sites n).ordinary_independent i⟩

theorem domain_fractionRing (hp : ∀ j i, primary j (MultiDomain.coordinate i) ≤ 1)
    (hg : ∀ p i, guard p (MultiDomain.coordinate i) ≤ 1) : IsFractionRing (domain C L primary guard) (FunctionField (r+1)) :=
  MultiDomain.fractionRing_of_coordinates _ (domain_coordinate C L primary guard hp hg)

theorem domain_normal [IsFractionRing (domain C L primary guard) (FunctionField (r+1))] :
    IsIntegrallyClosed (domain C L primary guard) := by
  let B := (horizontal C L).toSubring
  let D := domain C L primary guard
  have hr : inverted (Set.range (main C L)) (family C L).puncture ≤ nonZeroDivisors (Poly r) := by
    apply Submonoid.closure_le.mpr
    rintro _ (⟨n,rfl⟩ | ⟨n,rfl⟩)
    · exact mem_nonZeroDivisors_iff_ne_zero.mpr (event C L n).irreducible.ne_zero
    · exact mem_nonZeroDivisors_iff_ne_zero.mpr ((family C L).irreducible n).ne_zero
  let : IsIntegrallyClosed (horizontal C L) := isIntegrallyClosed_of_isLocalization _ _ hr
  let : IsFractionRing B (FunctionField (r+1)) := inferInstanceAs (IsFractionRing (horizontal C L) (FunctionField (r+1)))
  let : IsIntegrallyClosedIn B (FunctionField (r+1)) := (isIntegrallyClosed_iff_isIntegrallyClosedIn (FunctionField (r+1))).mp
    (inferInstanceAs (IsIntegrallyClosed (horizontal C L)))
  apply Subring.isIntegrallyClosed_iff.mpr
  intro x hx
  have hmem (S : Subring (FunctionField (r+1))) [IsIntegrallyClosedIn S (FunctionField (r+1))] (hs : D ≤ S) : x ∈ S :=
    Subring.isIntegrallyClosedIn_iff.mp inferInstance
      (IsIntegral.map_of_comp_eq (Subring.inclusion hs) (RingHom.id (FunctionField (r+1))) rfl hx)
  apply (mem_intersection _ _ _).mpr
  refine ⟨hmem B (intersection_le _ _), fun i ↦ ?_⟩
  let V := (branchVal C L primary guard i).valuationSubring
  let : IsFractionRing V.toSubring (FunctionField (r+1)) := inferInstanceAs (IsFractionRing V (FunctionField (r+1)))
  let : IsIntegrallyClosedIn V.toSubring (FunctionField (r+1)) :=
    (isIntegrallyClosed_iff_isIntegrallyClosedIn (FunctionField (r+1))).mp inferInstance
  exact hmem V.toSubring (fun y hy ↦ ((mem_intersection _ _ _).mp hy).2 i)

instance domainHorizontalAlgebra : Algebra (domain C L primary guard) (horizontal C L) :=
  (Subring.inclusion (show domain C L primary guard ≤ (horizontal C L).toSubring from intersection_le _ _)).toAlgebra

theorem unit_branch_value (u : (domain C L primary guard)ˣ) (i : Branch) :
    branchVal C L primary guard i ((u : domain C L primary guard) : (FunctionField (r+1))) = 1 := by
  let v := branchVal C L primary guard i
  have h (a : (domain C L primary guard)ˣ) : v ((a : domain C L primary guard) : (FunctionField (r+1))) ≤ 1 :=
    ((mem_intersection _ _ _).mp (a : domain C L primary guard).property).2 i
  apply le_antisymm (h u)
  have he : v ((u : domain C L primary guard) : (FunctionField (r+1))) * v ((u⁻¹ : (domain C L primary guard)ˣ).val : (FunctionField (r+1))) = 1 := by
    rw [← map_mul]
    change v (((u * u⁻¹).val : domain C L primary guard) : (FunctionField (r+1))) = 1
    simp
  exact he ▸ (mul_le_of_le_one_right zero_le (h u⁻¹))

theorem unit_main_word (u : (domain C L primary guard)ˣ) :
    ∃ q : ℚ, q ≠ 0 ∧ ∃ a : ℕ →₀ ℤ, ((u : domain C L primary guard) : (FunctionField (r+1))) =
      (q : (FunctionField (r+1))) * PrincipalProfiles.word ((family C L).generator mixedPower) a := by
  let w := Units.map (algebraMap (domain C L primary guard) (horizontal C L)).toMonoidHom u
  apply pole_unit_elimination C L w
  intro n
  have h1 := unit_branch_value C L primary guard u (.inr (n,false))
  have h2 := unit_branch_value C L primary guard u (.inr (n,true))
  change _ = _
  exact congrArg (fun x : ℤᵐ⁰ ↦ -log x) (h1.trans h2.symm)

/-- Equal private and ordinary orders remove each auxiliary exponent. The ordinary
guard at every rational prime then forces the scalar in the normalized word to be a sign. -/
theorem pole_signed_main_word (u : (horizontal C L)ˣ)
    (hpair : ∀ n, DiscreteOrders.order ((family C L).places.auxiliary n) ((u : horizontal C L) : FunctionField (r+1)) =
      DiscreteOrders.order ((family C L).places.ordinary n) ((u : horizontal C L) : FunctionField (r+1)))
    (hg : ∀ p : PrimeIndex, guard p (p.val : FunctionField (r+1)) < 1)
    (hu : ∀ p, guard p ((u : horizontal C L) : FunctionField (r+1)) = 1)
    (hgen : ∀ p i, guard p ((family C L).generator mixedPower i) = 1) :
    ∃ a : ℕ →₀ ℤ, ((u : horizontal C L) : FunctionField (r+1)) = PrincipalProfiles.word ((family C L).generator mixedPower) a ∨
      ((u : horizontal C L) : FunctionField (r+1)) = -PrincipalProfiles.word ((family C L).generator mixedPower) a := by
  obtain ⟨q,_,a,ha⟩ := pole_unit_elimination C L u hpair
  have hs := MultiDomain.sign_of_guard_units guard hg q (fun p ↦ by
    have h := hu p
    rw [ha, map_mul, show guard p (PrincipalProfiles.word _ a) = 1 from
      RationalSigns.valuation_finsupp_prod_eq_one _ _ _ (hgen p), mul_one] at h
    exact h)
  refine ⟨a,?_⟩
  rcases hs with rfl | rfl <;> simp_all

theorem unit_signed_main_word (u : (domain C L primary guard)ˣ)
    (hg : ∀ p : PrimeIndex, guard p (p.val : (FunctionField (r+1))) < 1)
    (hgen : ∀ p i, guard p ((family C L).generator mixedPower i) = 1) :
    ∃ a : ℕ →₀ ℤ, ((u : domain C L primary guard) : (FunctionField (r+1))) = PrincipalProfiles.word ((family C L).generator mixedPower) a ∨
      ((u : domain C L primary guard) : (FunctionField (r+1))) = -PrincipalProfiles.word ((family C L).generator mixedPower) a := by
  obtain ⟨q,_,a,ha⟩ := unit_main_word C L primary guard u
  have hq := MultiDomain.sign_of_guard_units guard hg q (fun p ↦ by
    have h := unit_branch_value C L primary guard u (.inl (.inr p))
    change guard p _ = 1 at h
    rw [ha, map_mul, show guard p (PrincipalProfiles.word _ a) = 1 from
      RationalSigns.valuation_finsupp_prod_eq_one _ _ _ (hgen p), mul_one] at h
    exact h)
  refine ⟨a,?_⟩
  rcases hq with rfl | rfl <;> simp_all

def branchPrime (primes : ℕ → PrimeIndex) : Branch → PrimeIndex
  | .inl (.inl j) => primes j
  | .inl (.inr p) => p
  | .inr (n,_) => (family C L).prime n

theorem branch_prime_value (primes : ℕ → PrimeIndex)
    (hp : ∀ j, primary j ((primes j).val : (FunctionField (r+1))) = exp (-1)) (hg : ∀ p, guard p (p.val : (FunctionField (r+1))) = exp (-1))
    (i : Branch) : branchVal C L primary guard i ((branchPrime C L primes i).val : (FunctionField (r+1))) = exp (-1) := by
  rcases i with (i|v)|⟨j,b⟩
  · exact hp i
  · exact hg v
  · cases b <;> apply EvaluationDVR.valuation_prime

/-- Negative vertical support is finite. The two new valuations incur no
additional hypothesis by finiteness of the concrete private support. -/
theorem finite_bad_branches (z : (FunctionField (r+1))) (hp : {j | 1 < primary j z}.Finite) (hg : {p | 1 < guard p z}.Finite) :
    {i | 1 < branchVal C L primary guard i z}.Finite := by
  apply Set.finite_preimage_inl_and_inr.mp
  refine ⟨Set.finite_preimage_inl_and_inr.mp ⟨hp,hg⟩,?_⟩
  by_cases hz : z = 0
  · subst z
    simp
  have h := (finite_support C L z hz).prod (Set.finite_univ : (Set.univ : Set Bool).Finite)
  apply h.subset
  rintro ⟨n,b⟩ hb
  refine ⟨?_,Set.mem_univ _⟩
  cases b
  · exact Or.inl (ne_of_gt hb)
  · exact Or.inr (ne_of_gt hb)

/-- Inverting all integer denominators in the enlarged intersection gives the actual
punctured horizontal localization. -/
theorem domain_integerLocalization (primes : ℕ → PrimeIndex)
    (hp : ∀ j, primary j ((primes j).val : (FunctionField (r+1))) = exp (-1)) (hg : ∀ p, guard p (p.val : (FunctionField (r+1))) = exp (-1))
    (hpf : ∀ z ∈ horizontal C L, {j | 1 < primary j z}.Finite)
    (hgf : ∀ z ∈ horizontal C L, {p | 1 < guard p z}.Finite) :
    IsLocalization (integerDenominators (domain C L primary guard)) (horizontal C L) :=
  integer_isLocalization ((horizontal C L).restrictScalars ℚ) (branchVal C L primary guard)
    (fun i ↦ (branchPrime C L primes i).val) (fun i ↦ (branchPrime C L primes i).property.pos)
    (branch_prime_value C L primary guard primes hp hg)
    (fun z hz ↦ finite_bad_branches C L primary guard z (hpf z hz) (hgf z hz))

theorem domain_dimension [IsLocalization (integerDenominators (domain C L primary guard)) (horizontal C L)]
    (hv : ∀ v : PrimeSpectrum (domain C L primary guard), ¬ Disjoint
      (integerDenominators (domain C L primary guard) : Set (domain C L primary guard)) v.asIdeal → Order.height v ≤ d) :
    ringKrullDim (domain C L primary guard) = d := by
  have hh := (family C L).pole_dimension (fun n ↦ (event C L n).irreducible)
  let m := integerDenominators (domain C L primary guard)
  refine le_antisymm (ringKrullDim_le_of_vertical_heights (horizontal C L) m d hh.le hv) ?_
  rw [← hh]
  apply Order.krullDim_le_of_strictMono (PrimeSpectrum.comap (algebraMap (domain C L primary guard) (horizontal C L)))
  exact fun _ _ h ↦ (IsLocalization.orderEmbedding m (horizontal C L)).strictMono h

end UnconditionalCounterexample.Variations.PrivateGuards.Live
