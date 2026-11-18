import UnconditionalCounterexample.PaperIdealProfiles

/-!
# Actual vertical singleton ideals

The source's existing primary/guard isolators are units of the pole algebra,
so they vanish in order at every retained horizontal place as well. The literal
two-generator ideal (p,f) has minimum order one at the chosen vertical place and
zero at every other place. Its actual finite generation and the proved DVR
stalks make it an invertible fractional ideal of PaperConstruction.domain.
-/

noncomputable section
namespace UnconditionalCounterexample.PaperIdealProfiles
open WithZero CompleteProfiles PaperConstruction FractionalIdealProfiles Polynomial GuardSupport
open scoped nonZeroDivisors
local instance : IsFractionRing domain (RatFunc ℚ) := fractionRing

abbrev Vertical := ℕ ⊕ PrimeIndex

def verticalLabel : Vertical → Label
  | .inl j => .primary j
  | .inr p => .outside (.inl p)

theorem valuation_vertical (i : Vertical) : v (verticalLabel i) = PairedDomain.vertical places i := by
  cases i <;> rfl

theorem verticalLabel_injective : Function.Injective verticalLabel := by
  intro i j h
  cases i <;> cases j <;> simp_all [verticalLabel]

/-- The already constructed isolator has order three at precisely one vertical
place and order zero at every horizontal as well as every other vertical place. -/
theorem exists_full_isolator (i : Vertical) :
    ∃ f : domain, f ≠ 0 ∧ ∀ l : Label,
      v l (f : RatFunc ℚ) = if l = verticalLabel i then exp (-3 : ℤ) else 1 := by
  classical
  obtain ⟨f, hfinv, hfi, hfother⟩ := PairedSpectrum.vertical_isolators raw exponent places
    generatorProfiles.b generatorProfiles.q generatorProfiles.guard i
  have hf0 : (f : RatFunc ℚ) ≠ 0 := by
    intro hz
    rw [hz, map_zero] at hfi
    exact exp_ne_zero hfi.symm
  have hB := ((IntersectionDomain.mem_intersection _ _ _).mp f.property).1
  have hS : ∀ q ∈ poles, q ≠ 0 := by
    intro q hq hz
    exact raw_constant hq (by simp [hz])
  have hh := (HorizontalOrders.mem_and_inv_mem_iff_retained_valuations_eq_one poles hS f hf0).mp
    ⟨hB, hfinv⟩
  have hv (j : Vertical) : v (verticalLabel j) (f : RatFunc ℚ) = if j = i then exp (-3 : ℤ) else 1 := by
    rw [valuation_vertical]
    split_ifs with h
    · simpa only [h] using hfi
    · exact hfother j h
  refine ⟨f, fun hz => hf0 (congrArg Subtype.val hz), ?_⟩
  intro l
  cases l with
  | limit =>
    have he := hh HorizontalOrders.xPoint
      (HorizontalOrders.retained_xPoint_of_constantCoeff_ne_zero poles (fun _ hq => raw_constant hq))
    cases i <;> simpa [verticalLabel, v, CompleteProfiles.valuations] using he
  | primary j =>
    have he := hv (.inl j)
    cases i <;> simpa [verticalLabel, v, CompleteProfiles.valuations] using he
  | outside o =>
    cases o with
    | inl p =>
      have he := hv (.inr p)
      cases i <;> simpa [verticalLabel, v, CompleteProfiles.valuations] using he
    | inr h =>
      have he := hh h.val h.property.1
      cases i <;> simpa [verticalLabel, v, CompleteProfiles.valuations] using he

def verticalPrime : Vertical → PrimeIndex := Sum.elim places.primes id

theorem prime_at_vertical (i : Vertical) :
    v (verticalLabel i) ((verticalPrime i).val : RatFunc ℚ) = exp (-1 : ℤ) := by
  rw [valuation_vertical]
  cases i with
  | inl j => exact EvaluationDVR.valuation_prime _ _
  | inr p => exact EvaluationDVR.valuation_prime _ _

/-- A two-generator fractional ideal (p,f) has the exact vertical singleton
profile, and is invertible by the actual DVR stalks of the constructed domain. -/
theorem exists_vertical_singleton (i : Vertical) :
    ∃ I : Fractionalˣ, HasProfile v I.val (fun l => if l = verticalLabel i then 1 else 0) := by
  classical
  obtain ⟨f, hf0, hf⟩ := exists_full_isolator i
  let p : RatFunc ℚ := (verticalPrime i).val
  have hp0 : p ≠ 0 := by
    dsimp only [p]
    exact Nat.cast_ne_zero.mpr (verticalPrime i).property.ne_zero
  have hfK : (f : RatFunc ℚ) ≠ 0 := fun h => hf0 (Subtype.ext h)
  let J : Fractional := FractionalIdeal.spanSingleton domain⁰ p + FractionalIdeal.spanSingleton domain⁰ (f : RatFunc ℚ)
  have hJ : HasProfile v J (fun l => if l = verticalLabel i then 1 else 0) := by
    intro l
    have hm := (hasValue_spanSingleton (v l) (integral l) p hp0).add
      (hasValue_spanSingleton (v l) (integral l) (f : RatFunc ℚ) hfK)
    have hfval : DiscreteOrders.order (v l) (f : RatFunc ℚ) = if l = verticalLabel i then 3 else 0 := by
      unfold DiscreteOrders.order
      rw [hf]
      split_ifs <;> simp
    have hpnonneg : 0 ≤ DiscreteOrders.order (v l) p :=
      (DiscreteOrders.order_nonneg_iff (v l) hp0).mpr (integral l ((verticalPrime i).val : domain))
    by_cases hl : l = verticalLabel i
    · have hpval : DiscreteOrders.order (v l) p = 1 := by
        subst l
        unfold DiscreteOrders.order
        rw [prime_at_vertical]
        simp
      rw [hfval, hpval, ite_eq_left hl, min_eq_left (by norm_num : (1 : ℤ) ≤ 3)] at hm
      simpa only [ite_eq_left hl] using hm
    · rw [hfval, ite_eq_right hl, min_eq_right hpnonneg] at hm
      simpa only [ite_eq_right hl] using hm
  have hfg : (J : Submodule domain (RatFunc ℚ)).FG := by
    rw [show J = FractionalIdeal.spanSingleton domain⁰ p + FractionalIdeal.spanSingleton domain⁰ (f : RatFunc ℚ) from rfl,
      FractionalIdeal.coe_add, FractionalIdeal.coe_spanSingleton, FractionalIdeal.coe_spanSingleton,
      Submodule.add_eq_sup]
    exact (Submodule.fg_span_singleton p).sup (Submodule.fg_span_singleton (f : RatFunc ℚ))
  have hu : IsUnit J := isUnit_of_fg J hfg (hJ (verticalLabel i)).ne_zero
  refine ⟨hu.unit, ?_⟩
  rw [hu.unit_spec]
  exact hJ

end UnconditionalCounterexample.PaperIdealProfiles
