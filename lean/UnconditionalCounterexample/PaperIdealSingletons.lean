import UnconditionalCounterexample.PaperIdealProfiles
import UnconditionalCounterexample.PairedResidues

/-!
# Actual vertical singleton ideals

The two-generator ideals (p,t) and (p,t-r) isolate the primary and guard
coordinates over p when r lifts the guard residue. Their orders are the
coordinatewise minima of the two generator orders. The same construction
also supplies element isolators, used in the direct spectrum proof.
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

/-- The literal two-generator fractional ideal $(p,t-r)$ in the common fraction field. -/
def parameterPair (p : PrimeIndex) (r : ℤ) : Fractional :=
  FractionalIdeal.spanSingleton domain⁰ (p.val : RatFunc ℚ) +
    FractionalIdeal.spanSingleton domain⁰ (RatFunc.X - (r : RatFunc ℚ))

private theorem translate_ne_zero (r : ℤ) : (RatFunc.X : RatFunc ℚ) - r ≠ 0 := by
  let : Algebra ℚ (RatFunc ℚ) := RatFunc.instAlgebraOfPolynomial ℚ ℚ
  intro hz
  have he := sub_eq_zero.mp hz
  exact (RatFunc.transcendental_X (K := ℚ)) (he ▸ isIntegral_intCast r).isAlgebraic

private theorem pair_has_min (p : PrimeIndex) (r : ℤ) (l : Label) :
    HasValue (parameterPair p r) (v l)
      (min (DiscreteOrders.order (v l) (p.val : RatFunc ℚ))
        (DiscreteOrders.order (v l) (RatFunc.X - (r : RatFunc ℚ)))) :=
  (hasValue_spanSingleton (v l) (integral l) _ (Nat.cast_ne_zero.mpr p.property.ne_zero)).add
    (hasValue_spanSingleton (v l) (integral l) _ (translate_ne_zero r))

theorem parameterPair_isUnit (p : PrimeIndex) (r : ℤ) : IsUnit (parameterPair p r) := by
  apply isUnit_of_fg _ _ (pair_has_min p r .limit).ne_zero
  unfold parameterPair
  rw [FractionalIdeal.coe_add, FractionalIdeal.coe_spanSingleton,
    FractionalIdeal.coe_spanSingleton, Submodule.add_eq_sup]
  exact (Submodule.fg_span_singleton _).sup (Submodule.fg_span_singleton _)

private theorem pair_at_unit_prime (p : PrimeIndex) (r : ℤ) (l : Label)
    (hp : v l (p.val : RatFunc ℚ) = 1) : HasValue (parameterPair p r) (v l) 0 := by
  have hx : RatFunc.X - (r : RatFunc ℚ) ∈ domain :=
    domain.sub_mem (PairedDomain.X_mem poles places) (intCast_mem domain r)
  have hpos := (DiscreteOrders.order_nonneg_iff (v l) (translate_ne_zero r)).mpr (integral l ⟨_, hx⟩)
  have hz := (DiscreteOrders.order_eq_zero_iff (v l) (Nat.cast_ne_zero.mpr p.property.ne_zero)).mpr hp
  simpa only [hz, min_eq_left hpos] using pair_has_min p r l

/-- On either evaluation branch over p, (p,t-r) has order one precisely
when the evaluation point reduces to r. -/
private theorem branch_min (p : PrimeIndex) (a : ℤ_[p.val]) (ha : Transcendental ℚ a.val) (r : ℤ) :
    let w := EvaluationDVR.evaluationValuation p.val a.val ha
    min (DiscreteOrders.order w (p.val : RatFunc ℚ))
      (DiscreteOrders.order w (RatFunc.X - (r : RatFunc ℚ))) =
        if PadicInt.toZMod a = (r : ZMod p.val) then 1 else 0 := by
  let w := EvaluationDVR.evaluationValuation p.val a.val ha
  change min (DiscreteOrders.order w _) (DiscreteOrders.order w _) = _
  have hp : DiscreteOrders.order w (p.val : RatFunc ℚ) = 1 := by
    simp [DiscreteOrders.order, w, EvaluationDVR.evaluationValuation]
  rw [hp]
  have hv : w (RatFunc.X - (r : RatFunc ℚ)) = Padic.mulValuation ((a - r : ℤ_[p.val]) : ℚ_[p.val]) := by
    simp [w, EvaluationDVR.evaluationValuation, EvaluationDVR.valuation]
  by_cases hr : PadicInt.toZMod a = (r : ZMod p.val)
  · have hn : ¬ IsUnit (a - r) := by simp [padicInt_isUnit_iff_toZMod_ne_zero, hr]
    have hvlt : w (RatFunc.X - (r : RatFunc ℚ)) < 1 := by
      rw [hv]
      simpa only [map_one] using (Padic.norm_lt_norm_iff_mulValuation_lt
        (x := ((a - r : ℤ_[p.val]) : ℚ_[p.val])) (y := 1)).mp
          (by simpa only [norm_one, ← PadicInt.norm_def] using PadicInt.not_isUnit_iff.mp hn)
    rw [DiscreteOrders.value_eq_exp_neg_order w (translate_ne_zero r), exp_lt_one_iff] at hvlt
    rw [ite_eq_left hr, min_eq_left (by omega)]
  · have hu : IsUnit (a - r) := by simpa [padicInt_isUnit_iff_toZMod_ne_zero, sub_eq_zero] using hr
    have hz : DiscreteOrders.order w (RatFunc.X - (r : RatFunc ℚ)) = 0 := by
      apply (DiscreteOrders.order_eq_zero_iff w (translate_ne_zero r)).mpr
      rw [hv]
      exact mulValuation_eq_one_of_norm_eq_one _ (PadicInt.isUnit_iff.mp hu)
    simp [hr, hz]

private theorem primary_residue_zero (j : ℕ) : PadicInt.toZMod (places.primary j) = 0 := by
  by_contra hn
  apply PairedResidues.primary_not_isUnit places _ j ((padicInt_isUnit_iff_toZMod_ne_zero _).mpr hn)
  apply PairedResidues.not_isUnit_of_valuation_pos
  have he : (places.primary 0).val.valuation = 2 := PrimaryChoices.primary_zero
  omega

private theorem guard_residue_ne_zero (p : PrimeIndex) : PadicInt.toZMod (places.guard p) ≠ 0 :=
  (padicInt_isUnit_iff_toZMod_ne_zero _).mp (construction.chain.guardChain.value_unit p)

private theorem horizontal_prime_unit (p : PrimeIndex) (h : PrincipalProfiles.MonicIrreducible ℚ) :
    HorizontalOrders.valuation h (p.val : RatFunc ℚ) = 1 := by
  simpa only [map_natCast] using HorizontalOrders.valuation_constant h (p.val : ℚ)
    (Nat.cast_ne_zero.mpr p.property.ne_zero)

/-- On all maximal-ideal labels, the order of (p,t-r) is obtained by checking
the residue of r at the two points over p. The prime itself is a unit elsewhere. -/
private theorem pair_fiber_profile (j : ℕ) (r : ℤ) :
    HasProfile v (parameterPair (places.primes j) r) (fun l => match l with
      | .primary k => if j = k ∧ (r : ZMod (places.primes j).val) = 0 then 1 else 0
      | .outside (.inl q) => if places.primes j = q ∧ PadicInt.toZMod (places.guard (places.primes j)) = r then 1 else 0
      | _ => 0) := by
  classical
  intro l
  cases l with
  | limit => exact pair_at_unit_prime _ _ _ (horizontal_prime_unit _ _)
  | primary k =>
    by_cases hk : j = k
    · subst k
      have hm := pair_has_min (places.primes j) r (.primary j)
      have he : min (DiscreteOrders.order (v (.primary j)) ((places.primes j).val : RatFunc ℚ))
          (DiscreteOrders.order (v (.primary j)) (RatFunc.X - (r : RatFunc ℚ))) =
          (if PadicInt.toZMod (places.primary j) = (r : ZMod _) then 1 else 0) :=
        branch_min _ _ (places.primary_trans j) r
      rw [he] at hm
      simpa [primary_residue_zero, eq_comm] using hm
    · simpa [hk] using pair_at_unit_prime (places.primes j) r (.primary k)
        (PairedResidues.valuation_prime_eq_one_of_ne _ _ _ (fun h => hk (places.primes.injective (Subtype.ext h))))
  | outside o =>
    cases o with
    | inr h => exact pair_at_unit_prime _ _ _ (horizontal_prime_unit _ _)
    | inl q =>
      by_cases hq : places.primes j = q
      · subst q
        have hm := pair_has_min (places.primes j) r (.outside (.inl (places.primes j)))
        have he : min (DiscreteOrders.order (v (.outside (.inl (places.primes j)))) ((places.primes j).val : RatFunc ℚ))
            (DiscreteOrders.order (v (.outside (.inl (places.primes j)))) (RatFunc.X - (r : RatFunc ℚ))) =
            (if PadicInt.toZMod (places.guard (places.primes j)) = (r : ZMod _) then 1 else 0) :=
          branch_min _ _ (places.guard_trans _) r
        rw [he] at hm
        simpa using hm
      · simpa [hq] using pair_at_unit_prime (places.primes j) r (.outside (.inl q))
          (PairedResidues.valuation_prime_eq_one_of_ne _ _ _ (fun h => hq (Subtype.ext h)))

/-- The invertible fractional ideal (p,t) has precisely the primary singleton profile. -/
theorem parameterIdeal_hasProfile (j : ℕ) :
    HasProfile v (FractionalIdeal.spanSingleton domain⁰ ((places.primes j).val : RatFunc ℚ) +
      FractionalIdeal.spanSingleton domain⁰ RatFunc.X)
      (fun l => if l = verticalLabel (.inl j) then 1 else 0) := by
  intro l
  have h := pair_fiber_profile j 0 l
  cases l with
  | limit => simpa [parameterPair, verticalLabel] using h
  | primary k => simpa [parameterPair, verticalLabel, eq_comm] using h
  | outside o =>
    cases o <;> simpa [parameterPair, verticalLabel, guard_residue_ne_zero] using h

/-- For any integer lift of the guard residue, the literal (p,t-r) has
precisely the guard singleton profile. -/
theorem shiftedParameterIdeal_hasProfile (p : PrimeIndex) (r : ℤ)
    (hr : (r : ZMod p.val) = PadicInt.toZMod (places.guard p)) :
    HasProfile v (parameterPair p r)
      (fun l => if l = verticalLabel (.inr p) then 1 else 0) := by
  obtain ⟨j, rfl⟩ := places.primes.surjective p
  have hn := guard_residue_ne_zero (places.primes j)
  intro l
  have h := pair_fiber_profile j r l
  cases l with
  | limit => simpa [verticalLabel] using h
  | primary k => simpa [verticalLabel, hr, hn] using h
  | outside o =>
    cases o <;> simpa [verticalLabel, hr, eq_comm] using h

/-- The two explicit ideals supply the vertical generators for profile realization. -/
theorem exists_vertical_singleton (i : Vertical) :
    ∃ I : Fractionalˣ, HasProfile v I.val (fun l => if l = verticalLabel i then 1 else 0) := by
  cases i with
  | inl j =>
    have hu := parameterPair_isUnit (places.primes j) 0
    refine ⟨hu.unit, ?_⟩
    rw [hu.unit_spec]
    simpa [parameterPair] using parameterIdeal_hasProfile j
  | inr p =>
    obtain ⟨r, hr⟩ := ZMod.intCast_surjective (PadicInt.toZMod (places.guard p))
    have hu := parameterPair_isUnit p r
    refine ⟨hu.unit, ?_⟩
    rw [hu.unit_spec]
    exact shiftedParameterIdeal_hasProfile p r hr

end UnconditionalCounterexample.PaperIdealProfiles
