import UnconditionalCounterexample.Variations.PrivateVerticalBranches
import UnconditionalCounterexample.Variations.PrivateGuardsTablePermanence
import UnconditionalCounterexample.Variations.PrivateGuardsDomain

/-! # Dimension, fraction field and normality of the chronological punctured domain

Every prime meeting the integers has height one. The generic fibre retains the
chosen flag and meets every prime of the next height. Both calculations refer
to the same subring of the specified rational function field.
-/

noncomputable section
namespace UnconditionalCounterexample.Variations.PrivateGuards.Live

open GuardSupport MvPolynomial MultiDomain MultivariateSelection IntersectionDomain WithZero

variable {r d : ℕ} {K : Type*} [Field K] [CharZero K]
  (P : TablePolicy r K) (q : PrimeIndex) (c : Fin (r+1) → ℚ) (C : Config r d)

local notation "L" => tableRule P q c
local notation "T" => publicPath P q c C
abbrev tablePrimaryVal (j : ℕ) := ((T).places.primary j).valuation
abbrev tableGuardVal (p : PrimeIndex) := ((T).places.guard p).valuation

local notation "pVal" => tablePrimaryVal P q c C
local notation "gVal" => tableGuardVal P q c C

/-- The punctured intersection on the permanent public and private places. -/
abbrev tableDomain := domain C L pVal gVal

theorem tableDomain_coordinate (i : Fin (r+1)) : coordinate i ∈ tableDomain P q c C :=
  domain_coordinate C L pVal gVal (fun j i => (((T).places.primary j).valuation_coordinate i).trans_le (((T).places.primary j).integral i))
    (fun p i => (((T).places.guard p).valuation_coordinate i).trans_le (((T).places.guard p).integral i)) i

theorem tableDomain_fraction : IsFractionRing (tableDomain P q c C) (FunctionField (r+1)) :=
  fractionRing_of_coordinates _ (tableDomain_coordinate P q c C)

theorem tableDomain_normal : IsIntegrallyClosed (tableDomain P q c C) := by
  let := tableDomain_fraction P q c C
  exact domain_normal C L _ _

/-- The first coordinate hyperplane survives every main and private inversion. -/
theorem horizontal_tVal_integral (z : FunctionField (r+1)) (hz : z ∈ horizontal C L) :
    tVal z ≤ 1 := by
  let M := inverted (Set.range (main C L)) (family C L).puncture
  let : (Ideal.span ({X 0} : Set (Poly r))).IsPrime := (Ideal.span_singleton_prime (X_ne_zero _)).mpr X_prime
  have hden : M ≤ (Ideal.span ({X 0} : Set (Poly r))).primeCompl := by
    apply Submonoid.closure_le.mpr
    rintro f (⟨j,rfl⟩ | ⟨j,rfl⟩)
    · exact fun h => first_not_dvd_main P q c C j (Ideal.mem_span_singleton.mp h)
    · exact fun h => first_not_dvd_puncture P q c C j (Ideal.mem_span_singleton.mp h)
  obtain ⟨⟨f,b⟩,h⟩ := IsLocalization.surj M (⟨z,hz⟩ : horizontal C L)
  have hunit := PrimeOrders.valuation_of_not_dvd X_prime (show ¬ X 0 ∣ (b : Poly r) from
    fun h => hden b.property (Ideal.mem_span_singleton.mpr h))
  have he : z * algebraMap (Poly r) (FunctionField (r+1)) (b : Poly r) = algebraMap _ _ f :=
    congrArg (horizontal C L).subtype h
  have hv := congrArg tVal he
  rw [map_mul,show tVal (algebraMap (Poly r) _ (b : Poly r)) = 1 from hunit,mul_one] at hv
  rw [hv]
  by_cases hf : f = 0
  · simp [hf]
  · exact (PrimeOrders.valuation_of_polynomial X_prime hf).trans_le (exp_le_one_iff.mpr (neg_nonpos.mpr (Int.natCast_nonneg _)))

theorem tableDomain_integerLocalization :
    IsLocalization (integerDenominators (tableDomain P q c C)) (horizontal C L) := by
  apply domain_integerLocalization C L pVal gVal (T).places.primes
  · intro j
    exact EvaluationDVR.valuation_prime _ _
  · intro p
    exact ((T).places.guard p).valuation_natCast p.val |>.trans ((T).places.guard_prime p)
  · intro z hz
    obtain ⟨N,hN⟩ := Filter.eventually_atTop.mp ((T).primary_eventually z)
    apply (Set.finite_Iio N).subset
    intro j hj
    exact lt_of_not_ge (fun h => (not_lt_of_ge ((hN j h).trans_le (horizontal_tVal_integral P q c C z hz))) hj)
  · intro z _
    by_cases hz : z = 0
    · simp [hz]
    · exact ((T).finite_guard z hz).subset (fun _ h => ne_of_gt h)

theorem tableDomain_vertical_height (t : PrimeSpectrum (tableDomain P q c C))
    (ht : ¬ Disjoint (integerDenominators (tableDomain P q c C) : Set (tableDomain P q c C)) t.asIdeal) :
    Order.height t = 1 := by
  apply @mixed_vertical_height_one r d c (Batch r) C L (T).places.primes (T).places.primary (fun p => ((T).permanentFibre p).guard)
    (horizontal C L).toSubring (branchVal C L pVal gVal) (tableDomain_fraction P q c C) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
    (T).places.injective (primary_ne_private P q c C) (tableDomain_coordinate P q c C 0) _ t ht
  intro p
  have h := ((horizontal C L).restrictScalars ℚ).algebraMap_mem ((p.val : ℚ)⁻¹)
  rw [map_inv₀,map_natCast] at h
  exact h

theorem tableDomain_dimension : ringKrullDim (tableDomain P q c C) = d := by
  let := tableDomain_integerLocalization P q c C
  apply domain_dimension C L pVal gVal
  intro t ht
  rw [tableDomain_vertical_height P q c C t ht]
  exact_mod_cast C.positive

end UnconditionalCounterexample.Variations.PrivateGuards.Live
