import UnconditionalCounterexample.PaperCenters
import UnconditionalCounterexample.ValuationIdealPowers
import UnconditionalCounterexample.HorizontalStalks
import UnconditionalCounterexample.RadicalIdealProducts

/-!
# Actual stalks and normalized principal orders

The canonical localizations at the named maximal ideals are identified with
the actual valuation rings. Their maximal-ideal powers are measured by the
already realized natural profiles, with no normalization change.
-/

noncomputable section
namespace UnconditionalCounterexample.PaperMaximalSpectrum
open WithZero PaperConstruction CompleteProfiles

local instance : Algebra ℚ (RatFunc ℚ) := RatFunc.instAlgebraOfPolynomial ℚ ℚ

instance valuationAlgebra (p : Point) : Algebra domain (valuation p).valuationSubring :=
  (inclusion p).toAlgebra

instance valuationScalarTower (p : Point) : IsScalarTower domain (valuation p).valuationSubring (RatFunc ℚ) :=
  IsScalarTower.of_algebraMap_eq (fun _ => rfl)

theorem vertical_isLocalization (i : Vertical) :
    IsLocalization (center (.inl i)).primeCompl (valuation (.inl i)).valuationSubring := by
  let := PaperConstruction.fractionRing
  have h (j : Vertical) : IsLocalization
      (IntersectionStalks.center (PoleAlgebra.generated poles).toSubring (PairedDomain.vertical places) j).primeCompl
      (PairedDomain.vertical places j).valuationSubring := by
    obtain ⟨f, hi, hf, ho⟩ := PairedSpectrum.vertical_isolators raw exponent places
      generatorProfiles.b generatorProfiles.q generatorProfiles.guard j
    exact IntersectionStalks.valuation_isLocalization _ _ j f 3 (by decide) hi hf ho
  cases i with
  | inl n => exact h (.inl n)
  | inr p => exact h (.inr p)

/-- The actual vertical stalk, as a D-algebra, is the actual evaluation valuation ring. -/
def verticalStalkEquiv (i : Vertical) :
    Localization.AtPrime (center (.inl i)) ≃ₐ[domain] (valuation (.inl i)).valuationSubring := by
  letI := vertical_isLocalization i
  exact IsLocalization.algEquiv (center (.inl i)).primeCompl _ _

@[simp] theorem verticalStalkEquiv_algebraMap (i : Vertical) (x : domain) :
    verticalStalkEquiv i (algebraMap domain (Localization.AtPrime (center (.inl i))) x) =
      inclusion (.inl i) x := (verticalStalkEquiv i).commutes x

def verticalPrime : Vertical → GuardSupport.PrimeIndex := Sum.elim places.primes id

@[simp] theorem vertical_prime_value (i : Vertical) :
    valuation (.inl i) ((verticalPrime i).val : RatFunc ℚ) = exp (-1 : ℤ) := by
  cases i with
  | inl n => exact EvaluationDVR.valuation_prime _ _
  | inr p => exact EvaluationDVR.valuation_prime _ _

/-- The rational prime is a normalized element of order one at either vertical branch. -/
def verticalUniformizer (i : Vertical) : (valuation (.inl i)).valuationSubring :=
  ⟨((verticalPrime i).val : RatFunc ℚ), by
    change valuation (.inl i) ((verticalPrime i).val : RatFunc ℚ) ≤ 1
    rw [vertical_prime_value]
    simp⟩

@[simp] theorem verticalUniformizer_value (i : Vertical) :
    valuation (.inl i) (verticalUniformizer i : RatFunc ℚ) = exp (-1 : ℤ) := vertical_prime_value i

/-- Exact local principal powers at every actual primary and guard. -/
theorem vertical_principal_power (i : Vertical) (x : domain) (hx : x ≠ 0) :
    (Ideal.span ({x} : Set domain)).map (algebraMap domain (Localization.AtPrime (center (.inl i)))) =
      IsLocalRing.maximalIdeal (Localization.AtPrime (center (.inl i))) ^
        PaperConstruction.valuationProfiles.value (label (.inl i)) x := by
  rw [Ideal.map_span, Set.image_singleton]
  have hxL : algebraMap domain (Localization.AtPrime (center (.inl i))) x ≠ 0 := by
    exact fun h => hx ((FaithfulSMul.algebraMap_injective domain _)
      (h.trans (map_zero _).symm))
  have h := ValuationIdealPowers.span_eq_maximalIdeal_pow_of_equiv
    (valuation (.inl i)) (verticalUniformizer i) (verticalUniformizer_value i)
    (verticalStalkEquiv i).toRingEquiv
    (algebraMap domain (Localization.AtPrime (center (.inl i))) x) hxL
  change Ideal.span {algebraMap domain (Localization.AtPrime (center (.inl i))) x} =
    IsLocalRing.maximalIdeal (Localization.AtPrime (center (.inl i))) ^
      DiscreteOrders.natOrder (valuation (.inl i))
        (verticalStalkEquiv i (algebraMap domain (Localization.AtPrime (center (.inl i))) x) : RatFunc ℚ) at h
  rw [verticalStalkEquiv_algebraMap] at h
  exact h

private theorem nonzero_poles : ∀ q ∈ poles, q ≠ 0 := by
  intro q hq hz
  exact raw_constant hq (by simp [hz])

/-- The horizontal valuation ring has the literal composite D→B→valuationRing algebra. -/
@[instance_reducible] def horizontalDomainAlgebra (p : Horizontal) :
    Algebra domain (HorizontalOrders.valuation p.val).valuationSubring :=
  ((HorizontalPrimes.valuationInclusion poles nonzero_poles p.val p.property).comp
    (algebraMap domain (PoleAlgebra.generated poles))).toAlgebra

/-- The integer-localization tower identifies the actual horizontal D-stalk. -/
theorem horizontal_isLocalization (p : Horizontal) :
    let _ := horizontalDomainAlgebra p
    IsLocalization (center (.inr p)).primeCompl (HorizontalOrders.valuation p.val).valuationSubring := by
  let := horizontalDomainAlgebra p
  let := HorizontalStalks.valuationAlgebra poles nonzero_poles p.val p.property
  let := PaperConstruction.integerLocalization
  let := HorizontalStalks.isLocalization_center poles nonzero_poles p.val p.property
  have : IsScalarTower domain (PoleAlgebra.generated poles)
      (HorizontalOrders.valuation p.val).valuationSubring :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have h := IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
    (IntersectionDomain.integerDenominators domain)
    (HorizontalOrders.valuation p.val).valuationSubring
    (HorizontalPrimes.center poles nonzero_poles p.val p.property)
  change IsLocalization.AtPrime (HorizontalOrders.valuation p.val).valuationSubring
    ((HorizontalPrimes.center poles nonzero_poles p.val p.property).under domain) at h
  simpa only [horizontal_center_under] using h

def horizontalStalkEquiv (p : Horizontal) :
    let _ := horizontalDomainAlgebra p
    Localization.AtPrime (center (.inr p)) ≃ₐ[domain] (HorizontalOrders.valuation p.val).valuationSubring := by
  let := horizontalDomainAlgebra p
  let := horizontal_isLocalization p
  exact IsLocalization.algEquiv (center (.inr p)).primeCompl _ _

@[simp] theorem horizontalStalkEquiv_algebraMap (p : Horizontal) (x : domain) :
    let _ := horizontalDomainAlgebra p
    (horizontalStalkEquiv p (algebraMap domain (Localization.AtPrime (center (.inr p))) x) : RatFunc ℚ) = x := by
  let := horizontalDomainAlgebra p
  rw [AlgEquiv.commutes]
  rfl

/-- The retained irreducible itself has normalized order one in its actual stalk. -/
def horizontalUniformizer (p : Horizontal) : (HorizontalOrders.valuation p.val).valuationSubring :=
  ⟨PrincipalProfiles.factor p.val, by
    change HorizontalOrders.valuation p.val (PrincipalProfiles.factor p.val) ≤ 1
    rw [HorizontalOrders.valuation_factor_self]
    simp⟩

@[simp] theorem horizontalUniformizer_value (p : Horizontal) :
    HorizontalOrders.valuation p.val (horizontalUniformizer p : RatFunc ℚ) = exp (-1 : ℤ) :=
  HorizontalOrders.valuation_factor_self p.val

/-- Exact local principal powers at every retained horizontal prime, including X. -/
theorem horizontal_principal_power (p : Horizontal) (x : domain) (hx : x ≠ 0) :
    (Ideal.span ({x} : Set domain)).map (algebraMap domain (Localization.AtPrime (center (.inr p)))) =
      IsLocalRing.maximalIdeal (Localization.AtPrime (center (.inr p))) ^
        PaperConstruction.valuationProfiles.value (label (.inr p)) x := by
  let := horizontalDomainAlgebra p
  rw [Ideal.map_span, Set.image_singleton]
  have hxL : algebraMap domain (Localization.AtPrime (center (.inr p))) x ≠ 0 := by
    exact fun h => hx ((FaithfulSMul.algebraMap_injective domain _)
      (h.trans (map_zero _).symm))
  have h := ValuationIdealPowers.span_eq_maximalIdeal_pow_of_equiv
    (HorizontalOrders.valuation p.val) (horizontalUniformizer p) (horizontalUniformizer_value p)
    (horizontalStalkEquiv p).toRingEquiv
    (algebraMap domain (Localization.AtPrime (center (.inr p))) x) hxL
  change Ideal.span {algebraMap domain (Localization.AtPrime (center (.inr p))) x} =
    IsLocalRing.maximalIdeal (Localization.AtPrime (center (.inr p))) ^
      DiscreteOrders.natOrder (HorizontalOrders.valuation p.val)
        (horizontalStalkEquiv p (algebraMap domain (Localization.AtPrime (center (.inr p))) x) : RatFunc ℚ) at h
  rw [horizontalStalkEquiv_algebraMap] at h
  have hv : DiscreteOrders.natOrder (HorizontalOrders.valuation p.val) (x : RatFunc ℚ) =
      PaperConstruction.valuationProfiles.value (label (.inr p)) x := by
    change DiscreteOrders.natOrder (HorizontalOrders.valuation p.val) (x : RatFunc ℚ) =
      DiscreteOrders.natOrder (valuation (.inr p)) (x : RatFunc ℚ)
    rw [valuation_horizontal]
  rwa [hv] at h

/-- Every named maximal ideal has the same exact exponent as the complete actual profile. -/
theorem point_principal_power (p : Point) (x : domain) (hx : x ≠ 0) :
    (Ideal.span ({x} : Set domain)).map (algebraMap domain (Localization.AtPrime (center p))) =
      IsLocalRing.maximalIdeal (Localization.AtPrime (center p)) ^
        PaperConstruction.valuationProfiles.value (label p) x := by
  cases p with
  | inl i => exact vertical_principal_power i x hx
  | inr p => exact horizontal_principal_power p x hx

@[simp] theorem order_point (p : Point) (x : domain) :
    order (pointEquivMaximal p) x = PaperConstruction.valuationProfiles.value (label p) x := by
  simp [order, labelEquivMaximal, pointEquivLabel]

/-- The exact all-maximal principal-power dictionary consumed by arbitrary-ideal SP. -/
theorem principal_power (M : Maximal) (x : domain) (hx : x ≠ 0) :
    RadicalIdealProducts.localIdeal M (Ideal.span {x}) =
      RadicalIdealProducts.localMaximal M ^ order M x := by
  obtain ⟨p, rfl⟩ := pointEquivMaximal.surjective M
  rw [order_point]
  exact point_principal_power p x hx

/-- Positive actual profile is exactly membership in the named maximal ideal. -/
theorem mem_center_iff_profile_pos (p : Point) (x : domain) (hx : x ≠ 0) :
    x ∈ center p ↔ 0 < PaperConstruction.valuationProfiles.value (label p) x := by
  rw [mem_center, DiscreteOrders.value_eq_exp_neg_order _ (fun h => hx (Subtype.ext h))]
  have hc := PaperConstruction.valuationProfiles_cast (label p) x hx
  change (PaperConstruction.valuationProfiles.value (label p) x : ℤ) =
    DiscreteOrders.order (valuation p) (x : RatFunc ℚ) at hc
  rw [← hc, exp_lt_one_iff]
  omega

/-- The all-maximal order dictionary detects actual ideal membership. -/
theorem mem_maximal_iff_order_pos (M : Maximal) (x : domain) (hx : x ≠ 0) :
    x ∈ M.val ↔ 0 < order M x := by
  obtain ⟨p, rfl⟩ := pointEquivMaximal.surjective M
  rw [order_point]
  exact mem_center_iff_profile_pos p x hx

end UnconditionalCounterexample.PaperMaximalSpectrum
