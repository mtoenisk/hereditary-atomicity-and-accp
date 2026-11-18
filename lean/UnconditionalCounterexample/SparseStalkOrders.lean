import UnconditionalCounterexample.SparseCenters
import UnconditionalCounterexample.ValuationIdealPowers
import UnconditionalCounterexample.HorizontalStalks
import UnconditionalCounterexample.RadicalIdealProducts

/-!
# Actual stalks and normalized principal orders

The canonical localizations at the named maximal ideals are identified with
the actual (valuation A) rings. Their maximal-ideal powers are measured by the
already realized natural profiles, with no normalization change.
-/

noncomputable section
namespace UnconditionalCounterexample.SparseMaximalSpectrum
open WithZero SparseProfileData SparseProfiles

local instance : Algebra ℚ (RatFunc ℚ) := RatFunc.instAlgebraOfPolynomial ℚ ℚ

variable (A : Data)

instance valuationAlgebra (p : (Point A)) : Algebra A.domain ((valuation A) p).valuationSubring :=
  ((inclusion A) p).toAlgebra

instance valuationScalarTower (p : (Point A)) : IsScalarTower A.domain ((valuation A) p).valuationSubring (RatFunc ℚ) :=
  IsScalarTower.of_algebraMap_eq (fun _ => rfl)

theorem vertical_isLocalization (i : Vertical) :
    IsLocalization ((center A) (.inl i)).primeCompl ((valuation A) (.inl i)).valuationSubring := by
  let := A.fractionRing
  have h (j : Vertical) : IsLocalization
      (IntersectionStalks.center (PoleAlgebra.generated A.poles).toSubring (SparsePrimaryDomain.vertical A.places) j).primeCompl
      (SparsePrimaryDomain.vertical A.places j).valuationSubring := by
    obtain ⟨f, k, hk, hi, hf, ho⟩ := SparseSpectrum.vertical_isolators A.raw A.exponent A.places
      A.columns.b A.columns.q A.columns.guard j
    exact IntersectionStalks.valuation_isLocalization _ _ j f k hk hi hf ho
  cases i with
  | inl n => exact h (.inl n)
  | inr p => exact h (.inr p)

/-- The actual vertical stalk, as a D-algebra, is the actual evaluation (valuation A) ring. -/
def verticalStalkEquiv (i : Vertical) :
    Localization.AtPrime ((center A) (.inl i)) ≃ₐ[A.domain] ((valuation A) (.inl i)).valuationSubring := by
  letI := (vertical_isLocalization A) i
  exact IsLocalization.algEquiv ((center A) (.inl i)).primeCompl _ _

@[simp] theorem verticalStalkEquiv_algebraMap (i : Vertical) (x : A.domain) :
    (verticalStalkEquiv A) i (algebraMap A.domain (Localization.AtPrime ((center A) (.inl i))) x) =
      (inclusion A) (.inl i) x := ((verticalStalkEquiv A) i).commutes x

def verticalPrime : Vertical → GuardSupport.PrimeIndex := Sum.elim A.places.primes id

@[simp] theorem vertical_prime_value (i : Vertical) :
    (valuation A) (.inl i) (((verticalPrime A) i).val : RatFunc ℚ) = exp (-1 : ℤ) := by
  cases i with
  | inl n => exact EvaluationDVR.valuation_prime _ _
  | inr p => exact EvaluationDVR.valuation_prime _ _

/-- The rational prime is a normalized element of (order A) one at either vertical branch. -/
def verticalUniformizer (i : Vertical) : ((valuation A) (.inl i)).valuationSubring :=
  ⟨(((verticalPrime A) i).val : RatFunc ℚ), by
    change (valuation A) (.inl i) (((verticalPrime A) i).val : RatFunc ℚ) ≤ 1
    rw [(vertical_prime_value A)]
    simp⟩

@[simp] theorem verticalUniformizer_value (i : Vertical) :
    (valuation A) (.inl i) ((verticalUniformizer A) i : RatFunc ℚ) = exp (-1 : ℤ) := (vertical_prime_value A) i

/-- Exact local principal powers at every actual primary and guard. -/
theorem vertical_principal_power (i : Vertical) (x : A.domain) (hx : x ≠ 0) :
    (Ideal.span ({x} : Set A.domain)).map (algebraMap A.domain (Localization.AtPrime ((center A) (.inl i)))) =
      IsLocalRing.maximalIdeal (Localization.AtPrime ((center A) (.inl i))) ^
        A.profiles.value ((label A) (.inl i)) x := by
  rw [Ideal.map_span, Set.image_singleton]
  have hxL : algebraMap A.domain (Localization.AtPrime ((center A) (.inl i))) x ≠ 0 := by
    exact fun h => hx ((FaithfulSMul.algebraMap_injective A.domain _)
      (h.trans (map_zero _).symm))
  have h := ValuationIdealPowers.span_eq_maximalIdeal_pow_of_equiv
    ((valuation A) (.inl i)) ((verticalUniformizer A) i) ((verticalUniformizer_value A) i)
    ((verticalStalkEquiv A) i).toRingEquiv
    (algebraMap A.domain (Localization.AtPrime ((center A) (.inl i))) x) hxL
  change Ideal.span {algebraMap A.domain (Localization.AtPrime ((center A) (.inl i))) x} =
    IsLocalRing.maximalIdeal (Localization.AtPrime ((center A) (.inl i))) ^
      DiscreteOrders.natOrder ((valuation A) (.inl i))
        ((verticalStalkEquiv A) i (algebraMap A.domain (Localization.AtPrime ((center A) (.inl i))) x) : RatFunc ℚ) at h
  rw [(verticalStalkEquiv_algebraMap A)] at h
  exact h

private theorem nonzero_poles : ∀ q ∈ A.poles, q ≠ 0 := by
  intro q hq hz
  exact A.constant_nonzero q hq (by simp [hz])

/-- The horizontal (valuation A) ring has the literal composite D→B→valuationRing algebra. -/
@[instance_reducible] def horizontalDomainAlgebra (p : (Horizontal A)) :
    Algebra A.domain (HorizontalOrders.valuation p.val).valuationSubring :=
  ((HorizontalPrimes.valuationInclusion A.poles (nonzero_poles A) p.val p.property).comp
    (algebraMap A.domain (PoleAlgebra.generated A.poles))).toAlgebra

/-- The integer-localization tower identifies the actual horizontal D-stalk. -/
theorem horizontal_isLocalization (p : (Horizontal A)) :
    let _ := (horizontalDomainAlgebra A) p
    IsLocalization ((center A) (.inr p)).primeCompl (HorizontalOrders.valuation p.val).valuationSubring := by
  let := (horizontalDomainAlgebra A) p
  let := HorizontalStalks.valuationAlgebra A.poles (nonzero_poles A) p.val p.property
  let := A.integerLocalization
  let := HorizontalStalks.isLocalization_center A.poles (nonzero_poles A) p.val p.property
  have : IsScalarTower A.domain (PoleAlgebra.generated A.poles)
      (HorizontalOrders.valuation p.val).valuationSubring :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have h := IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
    (IntersectionDomain.integerDenominators A.domain)
    (HorizontalOrders.valuation p.val).valuationSubring
    (HorizontalPrimes.center A.poles (nonzero_poles A) p.val p.property)
  change IsLocalization.AtPrime (HorizontalOrders.valuation p.val).valuationSubring
    ((HorizontalPrimes.center A.poles (nonzero_poles A) p.val p.property).under A.domain) at h
  simpa only [(horizontal_center_under A)] using h

def horizontalStalkEquiv (p : (Horizontal A)) :
    let _ := (horizontalDomainAlgebra A) p
    Localization.AtPrime ((center A) (.inr p)) ≃ₐ[A.domain] (HorizontalOrders.valuation p.val).valuationSubring := by
  let := (horizontalDomainAlgebra A) p
  let := (horizontal_isLocalization A) p
  exact IsLocalization.algEquiv ((center A) (.inr p)).primeCompl _ _

@[simp] theorem horizontalStalkEquiv_algebraMap (p : (Horizontal A)) (x : A.domain) :
    let _ := (horizontalDomainAlgebra A) p
    ((horizontalStalkEquiv A) p (algebraMap A.domain (Localization.AtPrime ((center A) (.inr p))) x) : RatFunc ℚ) = x := by
  let := (horizontalDomainAlgebra A) p
  rw [AlgEquiv.commutes]
  rfl

/-- The retained irreducible itself has normalized (order A) one in its actual stalk. -/
def horizontalUniformizer (p : (Horizontal A)) : (HorizontalOrders.valuation p.val).valuationSubring :=
  ⟨PrincipalProfiles.factor p.val, by
    change HorizontalOrders.valuation p.val (PrincipalProfiles.factor p.val) ≤ 1
    rw [HorizontalOrders.valuation_factor_self]
    simp⟩

@[simp] theorem horizontalUniformizer_value (p : (Horizontal A)) :
    HorizontalOrders.valuation p.val ((horizontalUniformizer A) p : RatFunc ℚ) = exp (-1 : ℤ) :=
  HorizontalOrders.valuation_factor_self p.val

/-- Exact local principal powers at every retained horizontal prime, including X. -/
theorem horizontal_principal_power (p : (Horizontal A)) (x : A.domain) (hx : x ≠ 0) :
    (Ideal.span ({x} : Set A.domain)).map (algebraMap A.domain (Localization.AtPrime ((center A) (.inr p)))) =
      IsLocalRing.maximalIdeal (Localization.AtPrime ((center A) (.inr p))) ^
        A.profiles.value ((label A) (.inr p)) x := by
  let := (horizontalDomainAlgebra A) p
  rw [Ideal.map_span, Set.image_singleton]
  have hxL : algebraMap A.domain (Localization.AtPrime ((center A) (.inr p))) x ≠ 0 := by
    exact fun h => hx ((FaithfulSMul.algebraMap_injective A.domain _)
      (h.trans (map_zero _).symm))
  have h := ValuationIdealPowers.span_eq_maximalIdeal_pow_of_equiv
    (HorizontalOrders.valuation p.val) ((horizontalUniformizer A) p) ((horizontalUniformizer_value A) p)
    ((horizontalStalkEquiv A) p).toRingEquiv
    (algebraMap A.domain (Localization.AtPrime ((center A) (.inr p))) x) hxL
  change Ideal.span {algebraMap A.domain (Localization.AtPrime ((center A) (.inr p))) x} =
    IsLocalRing.maximalIdeal (Localization.AtPrime ((center A) (.inr p))) ^
      DiscreteOrders.natOrder (HorizontalOrders.valuation p.val)
        ((horizontalStalkEquiv A) p (algebraMap A.domain (Localization.AtPrime ((center A) (.inr p))) x) : RatFunc ℚ) at h
  rw [(horizontalStalkEquiv_algebraMap A)] at h
  have hv : DiscreteOrders.natOrder (HorizontalOrders.valuation p.val) (x : RatFunc ℚ) =
      A.profiles.value ((label A) (.inr p)) x := by
    change DiscreteOrders.natOrder (HorizontalOrders.valuation p.val) (x : RatFunc ℚ) =
      DiscreteOrders.natOrder ((valuation A) (.inr p)) (x : RatFunc ℚ)
    rw [(valuation_horizontal A)]
  rwa [hv] at h

/-- Every named maximal ideal has the same exact A.exponent as the complete actual profile. -/
theorem point_principal_power (p : (Point A)) (x : A.domain) (hx : x ≠ 0) :
    (Ideal.span ({x} : Set A.domain)).map (algebraMap A.domain (Localization.AtPrime ((center A) p))) =
      IsLocalRing.maximalIdeal (Localization.AtPrime ((center A) p)) ^
        A.profiles.value ((label A) p) x := by
  cases p with
  | inl i => exact (vertical_principal_power A) i x hx
  | inr p => exact (horizontal_principal_power A) p x hx

@[simp] theorem order_point (p : (Point A)) (x : A.domain) :
    (order A) ((pointEquivMaximal A) p) x = A.profiles.value ((label A) p) x := by
  simp [order, labelEquivMaximal, pointEquivLabel]

/-- The exact all-maximal principal-power dictionary consumed by arbitrary-ideal SP. -/
theorem principal_power (M : (Maximal A)) (x : A.domain) (hx : x ≠ 0) :
    RadicalIdealProducts.localIdeal M (Ideal.span {x}) =
      RadicalIdealProducts.localMaximal M ^ (order A) M x := by
  obtain ⟨p, rfl⟩ := (pointEquivMaximal A).surjective M
  rw [(order_point A)]
  exact (point_principal_power A) p x hx

/-- Positive actual profile is exactly membership in the named maximal ideal. -/
theorem mem_center_iff_profile_pos (p : (Point A)) (x : A.domain) (hx : x ≠ 0) :
    x ∈ (center A) p ↔ 0 < A.profiles.value ((label A) p) x := by
  rw [(mem_center A), DiscreteOrders.value_eq_exp_neg_order _ (fun h => hx (Subtype.ext h))]
  have hc := A.profiles_cast ((label A) p) x hx
  change (A.profiles.value ((label A) p) x : ℤ) =
    DiscreteOrders.order ((valuation A) p) (x : RatFunc ℚ) at hc
  rw [← hc, exp_lt_one_iff]
  omega

/-- The all-maximal (order A) dictionary detects actual ideal membership. -/
theorem mem_maximal_iff_order_pos (M : (Maximal A)) (x : A.domain) (hx : x ≠ 0) :
    x ∈ M.val ↔ 0 < (order A) M x := by
  obtain ⟨p, rfl⟩ := (pointEquivMaximal A).surjective M
  rw [(order_point A)]
  exact (mem_center_iff_profile_pos A) p x hx

end UnconditionalCounterexample.SparseMaximalSpectrum
