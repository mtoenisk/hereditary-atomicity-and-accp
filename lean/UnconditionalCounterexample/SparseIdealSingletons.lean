import UnconditionalCounterexample.SparseIdealProfiles

/-!
# Singleton ideal profiles in the sparse construction

The literal two-generator ideal (p,f) has profile one at its chosen vertical
place and zero elsewhere. The isolator f may have any positive order: selected
primary primes use the paired cubic isolators, while an omitted prime has only
its guard and admits the prime itself as an order-one isolator.
-/

noncomputable section
namespace UnconditionalCounterexample.SparseIdealProfiles
open WithZero SparseProfiles SparseProfileData FractionalIdealProfiles Polynomial GuardSupport
open scoped nonZeroDivisors
variable (A : Data)
local instance : IsFractionRing A.domain (RatFunc ℚ) := A.fractionRing

abbrev Vertical := ℕ ⊕ PrimeIndex

def verticalLabel : Vertical → A.Label
  | .inl j => .primary j
  | .inr p => .outside (.inl p)

theorem valuation_vertical (i : Vertical) : v A (verticalLabel A i) = SparsePrimaryDomain.vertical A.places i := by
  cases i <;> rfl

theorem verticalLabel_injective : Function.Injective (verticalLabel A) := by
  intro i j h
  cases i <;> cases j <;> simp_all [verticalLabel]

/-- The already constructed isolator has positive order at precisely one vertical
place and order zero at every horizontal as well as every other vertical place. -/
theorem exists_full_isolator (i : Vertical) :
    ∃ f : A.domain, ∃ k : ℕ, 0 < k ∧ f ≠ 0 ∧ ∀ l : A.Label,
      v A l (f : RatFunc ℚ) = if l = verticalLabel A i then exp (-(k : ℤ)) else 1 := by
  classical
  obtain ⟨f, k, hk, hfinv, hfi, hfother⟩ := SparseSpectrum.vertical_isolators A.raw A.exponent A.places
    A.columns.b A.columns.q A.columns.guard i
  have hf0 : (f : RatFunc ℚ) ≠ 0 := by
    intro hz
    rw [hz, map_zero] at hfi
    exact exp_ne_zero hfi.symm
  have hB := ((IntersectionDomain.mem_intersection _ _ _).mp f.property).1
  have hS : ∀ q ∈ A.poles, q ≠ 0 := by
    rintro q ⟨j, rfl⟩
    exact A.raw_ne_zero j
  have hh := (HorizontalOrders.mem_and_inv_mem_iff_retained_valuations_eq_one A.poles hS f hf0).mp
    ⟨hB, hfinv⟩
  have hv (j : Vertical) : v A (verticalLabel A j) (f : RatFunc ℚ) = if j = i then exp (-(k : ℤ)) else 1 := by
    rw [valuation_vertical A]
    split_ifs with h
    · simpa only [h] using hfi
    · exact hfother j h
  refine ⟨f, k, hk, fun hz => hf0 (congrArg Subtype.val hz), ?_⟩
  intro l
  cases l with
  | limit =>
    have he := hh HorizontalOrders.xPoint
      (HorizontalOrders.retained_xPoint_of_constantCoeff_ne_zero A.poles A.constant_nonzero)
    cases i <;> simpa [verticalLabel, v, SparseProfiles.valuations, Data.valuations] using he
  | primary j =>
    have he := hv (.inl j)
    cases i <;> simpa [verticalLabel, v, SparseProfiles.valuations, Data.valuations] using he
  | outside o =>
    cases o with
    | inl p =>
      have he := hv (.inr p)
      cases i <;> simpa [verticalLabel, v, SparseProfiles.valuations, Data.valuations] using he
    | inr h =>
      have he := hh h.val h.property.1
      cases i <;> simpa [verticalLabel, v, SparseProfiles.valuations, Data.valuations] using he

def verticalPrime : Vertical → PrimeIndex := Sum.elim A.places.primes id

theorem prime_at_vertical (i : Vertical) :
    v A (verticalLabel A i) ((verticalPrime A i).val : RatFunc ℚ) = exp (-1 : ℤ) := by
  rw [valuation_vertical A]
  cases i with
  | inl j => exact EvaluationDVR.valuation_prime _ _
  | inr p => exact EvaluationDVR.valuation_prime _ _

/-- A two-generator fractional ideal (p,f) has the exact vertical singleton
profile, and is invertible by the actual DVR stalks of the constructed domain. -/
theorem exists_vertical_singleton (i : Vertical) :
    ∃ I : (Fractional A)ˣ, HasProfile (v A) I.val (fun l => if l = verticalLabel A i then 1 else 0) := by
  classical
  obtain ⟨f, k, hk, hf0, hf⟩ := exists_full_isolator A i
  let p : RatFunc ℚ := (verticalPrime A i).val
  have hp0 : p ≠ 0 := by
    dsimp only [p]
    exact Nat.cast_ne_zero.mpr (verticalPrime A i).property.ne_zero
  have hfK : (f : RatFunc ℚ) ≠ 0 := fun h => hf0 (Subtype.ext h)
  let J : Fractional A := FractionalIdeal.spanSingleton A.domain⁰ p + FractionalIdeal.spanSingleton A.domain⁰ (f : RatFunc ℚ)
  have hJ : HasProfile (v A) J (fun l => if l = verticalLabel A i then 1 else 0) := by
    intro l
    have hm := (hasValue_spanSingleton (v A l) (integral A l) p hp0).add
      (hasValue_spanSingleton (v A l) (integral A l) (f : RatFunc ℚ) hfK)
    have hfval : DiscreteOrders.order (v A l) (f : RatFunc ℚ) = if l = verticalLabel A i then (k : ℤ) else 0 := by
      unfold DiscreteOrders.order
      rw [hf]
      split_ifs <;> simp
    have hpnonneg : 0 ≤ DiscreteOrders.order (v A l) p :=
      (DiscreteOrders.order_nonneg_iff (v A l) hp0).mpr (integral A l ((verticalPrime A i).val : A.domain))
    by_cases hl : l = verticalLabel A i
    · have hpval : DiscreteOrders.order (v A l) p = 1 := by
        subst l
        unfold DiscreteOrders.order
        rw [prime_at_vertical A]
        simp
      rw [hfval, hpval, ite_eq_left hl, min_eq_left (by omega : (1 : ℤ) ≤ k)] at hm
      simpa only [ite_eq_left hl] using hm
    · rw [hfval, ite_eq_right hl, min_eq_right hpnonneg] at hm
      simpa only [ite_eq_right hl] using hm
  have hfg : (J : Submodule A.domain (RatFunc ℚ)).FG := by
    rw [show J = FractionalIdeal.spanSingleton A.domain⁰ p + FractionalIdeal.spanSingleton A.domain⁰ (f : RatFunc ℚ) from rfl,
      FractionalIdeal.coe_add, FractionalIdeal.coe_spanSingleton, FractionalIdeal.coe_spanSingleton,
      Submodule.add_eq_sup]
    exact (Submodule.fg_span_singleton p).sup (Submodule.fg_span_singleton (f : RatFunc ℚ))
  have hu : IsUnit J := isUnit_of_fg A J hfg (hJ (verticalLabel A i)).ne_zero
  refine ⟨hu.unit, ?_⟩
  rw [hu.unit_spec]
  exact hJ

end UnconditionalCounterexample.SparseIdealProfiles
