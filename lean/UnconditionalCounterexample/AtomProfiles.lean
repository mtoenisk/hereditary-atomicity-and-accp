import UnconditionalCounterexample.CompleteProfiles
import UnconditionalCounterexample.ReturnPrefix

/-!
# The actual return elements are atoms

The literal recurrence a₀=X and aₙ₊₁=aₙbₙ₊₁/qₙ has the prescribed primary,
guard and horizontal profiles. Actual membership and irreducibility follow.
-/

noncomputable section
namespace UnconditionalCounterexample.AtomProfiles
open Polynomial WithZero CompleteProfiles PrimaryWordProfiles NormalizedWords
open GuardSupport DiscreteOrders

local instance : Algebra ℚ (RatFunc ℚ) := RatFunc.instAlgebraOfPolynomial ℚ ℚ

/-- The elementary row identity for the actual return recurrence. -/
theorem primary_recurrence (n j : ℕ) :
    primaryAtomProfile (n + 1) j = primaryAtomProfile n j + bWeight (n + 1) j - qWeight n j := by
  simp only [primaryAtomProfile, bWeight, qWeight]
  split_ifs <;> omega

/-- Compute the primary valuations of the literal rational recurrence. -/
theorem a_primary_valuation (U : ℕ → RatFunc ℚ)
    (v : ℕ → Valuation (RatFunc ℚ) ℤᵐ⁰)
    (hb : ∀ n j, v j (U (Generator.b n).stage) = exp (-(bWeight n j)))
    (hq : ∀ n j, v j (U (Generator.q n).stage) = exp (-(qWeight n j)))
    (hX : ∀ j, v j RatFunc.X = exp (-(primaryAtomProfile 0 j))) (n j : ℕ) :
    v j (ReturnPrefix.a U n) = exp (-(primaryAtomProfile n j)) := by
  induction n with
  | zero => exact hX j
  | succ n ih =>
    rw [ReturnPrefix.a_succ, map_div₀, map_mul]
    change v j (ReturnPrefix.a U n) * v j (U (Generator.b (n + 1)).stage) /
      v j (U (Generator.q n).stage) = _
    rw [ih, hb, hq, ← exp_add, ← exp_sub, primary_recurrence]
    congr 1
    ring

/-- At every place where all normalized generators are units, a_n keeps X's value. -/
theorem a_valuation_eq_X (U : ℕ → RatFunc ℚ) (v : Valuation (RatFunc ℚ) ℤᵐ⁰)
    (hU : ∀ i, v (U i) = 1) (n : ℕ) : v (ReturnPrefix.a U n) = v RatFunc.X := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [ReturnPrefix.a_succ, map_div₀, map_mul]
    change v (ReturnPrefix.a U n) * v (U (Generator.b (n + 1)).stage) /
      v (U (Generator.q n).stage) = _
    rw [ih, hU, hU, mul_one, div_one]

theorem primary_X_valuation (d : PairedDomain.Places)
    (hfirst : (d.primary 0).val.valuation = 2) (j : ℕ) :
    PairedDomain.vertical d (.inl j) RatFunc.X = exp (-(primaryAtomProfile 0 j)) := by
  change EvaluationDVR.evaluationValuation _ _ _ RatFunc.X = _
  rw [EvaluationDVR.evaluationValuation_X]
  have hv : (d.primary j).val.valuation = (if j = 0 then 2 else 1) := by
    by_cases hj : j = 0
    · subst j
      simpa using hfirst
    · simpa [hj] using d.primary_late j (Nat.pos_of_ne_zero hj)
  have hn : (d.primary j).val ≠ 0 := by
    intro hz
    simp only [hz, Padic.valuation_zero] at hv
    split_ifs at hv <;> norm_num at hv
  simp [Padic.mulValuation, hn, hv, primaryAtomProfile]

theorem guard_X_valuation (d : PairedDomain.Places) (hguard : ∀ p, IsUnit (d.guard p))
    (p : PrimeIndex) : PairedDomain.vertical d (.inr p) RatFunc.X = 1 := by
  change EvaluationDVR.evaluationValuation _ _ _ RatFunc.X = _
  rw [EvaluationDVR.evaluationValuation_X]
  apply GuardSupport.mulValuation_eq_one_of_norm_eq_one
  exact PadicInt.isUnit_iff.mp (hguard p)

/-- Both the normalized generator and its inverse belong to the actual pole algebra. -/
theorem generators_pole_unit (F : ℕ → ℚ[X]) (E : ℕ → ℕ) (j : ℕ) :
    generators F E j ∈ PoleAlgebra.generated (Set.range F) ∧
      (generators F E j)⁻¹ ∈ PoleAlgebra.generated (Set.range F) := by
  let B := PoleAlgebra.generated (Set.range F)
  have hp (i : ℕ) : algebraMap ℚ[X] (RatFunc ℚ) (F i) ∈ B := PoleAlgebra.polynomial_mem _ _
  have hi (i : ℕ) : (algebraMap ℚ[X] (RatFunc ℚ) (F i))⁻¹ ∈ B :=
    PoleAlgebra.inverse_mem (Set.mem_range_self i)
  have hprod : (∏ i ∈ Finset.range j, algebraMap ℚ[X] (RatFunc ℚ) (F i) ^ E j) ∈ B :=
    B.prod_mem (fun i _ => B.pow_mem (hp i) _)
  have hprodi : (∏ i ∈ Finset.range j, algebraMap ℚ[X] (RatFunc ℚ) (F i) ^ E j)⁻¹ ∈ B := by
    rw [← Finset.prod_inv_distrib]
    apply B.prod_mem
    intro i _
    rw [← inv_pow]
    exact B.pow_mem (hi i) _
  change _ / _ ∈ B ∧ (_ / _)⁻¹ ∈ B
  rw [div_eq_mul_inv, mul_inv_rev, inv_inv]
  exact ⟨B.mul_mem (hp j) hprodi, B.mul_mem hprod (hi j)⟩

/-- Every retained horizontal valuation of a normalized generator is one. -/
theorem generators_horizontal_valuation (F : ℕ → ℚ[X]) (E : ℕ → ℕ)
    (hF : ∀ i, F i ≠ 0) (p : PrincipalProfiles.MonicIrreducible ℚ)
    (hp : HorizontalOrders.Retained (Set.range F) p) (j : ℕ) :
    HorizontalOrders.valuation p (generators F E j) = 1 := by
  have hn : ∀ q ∈ Set.range F, q ≠ 0 := by
    rintro q ⟨i, rfl⟩
    exact hF i
  exact (HorizontalOrders.mem_and_inv_mem_iff_retained_valuations_eq_one _ hn _
    (ReturnPrefix.generators_ne_zero F E hF j)).mp (generators_pole_unit F E j) p hp

section Actual

variable (F : ℕ → ℚ[X]) (E : ℕ → ℕ) (d : PairedDomain.Places)
  (hG : GeneratorProfiles F E d) (hfirst : (d.primary 0).val.valuation = 2)
  (hguards : ∀ p, IsUnit (d.guard p))

include hG hfirst in
theorem a_primary (n j : ℕ) :
    PairedDomain.vertical d (.inl j) (ReturnPrefix.a (generators F E) n) =
      exp (-(primaryAtomProfile n j)) :=
  a_primary_valuation _ _ hG.b hG.q (primary_X_valuation d hfirst) n j

include hG hguards in
theorem a_guard (n : ℕ) (p : PrimeIndex) :
    PairedDomain.vertical d (.inr p) (ReturnPrefix.a (generators F E) n) = 1 := by
  rw [a_valuation_eq_X _ _ (hG.guard p), guard_X_valuation d hguards]

theorem a_pole_mem (n : ℕ) :
    ReturnPrefix.a (generators F E) n ∈ PoleAlgebra.generated (Set.range F) := by
  induction n with
  | zero => exact PoleAlgebra.X_mem _
  | succ n ih =>
    rw [ReturnPrefix.a_succ, div_eq_mul_inv]
    exact (PoleAlgebra.generated _).mul_mem
      ((PoleAlgebra.generated _).mul_mem ih
        (generators_pole_unit F E (Generator.b (n + 1)).stage).1)
      (generators_pole_unit F E (Generator.q n).stage).2

include hG hfirst hguards in
theorem a_mem (n : ℕ) :
    ReturnPrefix.a (generators F E) n ∈ PairedDomain.domain (Set.range F) d := by
  apply (IntersectionDomain.mem_intersection _ _ _).mpr
  refine ⟨a_pole_mem F E n, ?_⟩
  rintro (j | p)
  · rw [a_primary F E d hG hfirst]
    exact exp_le_one_iff.mpr (neg_nonpos.mpr (primaryAtomProfile_nonneg n j))
  · rw [a_guard F E d hG hguards]

/-- The canonical recurrence as an element of the actual domain. -/
def aElement (n : ℕ) : PairedDomain.domain (Set.range F) d :=
  ⟨ReturnPrefix.a (generators F E) n, a_mem F E d hG hfirst hguards n⟩

@[simp] theorem coe_aElement (n : ℕ) :
    (aElement F E d hG hfirst hguards n : RatFunc ℚ) = ReturnPrefix.a (generators F E) n := rfl

theorem aElement_ne_zero (hF : ∀ j, F j ≠ 0) (n : ℕ) :
    aElement F E d hG hfirst hguards n ≠ 0 := by
  intro h
  exact ReturnPrefix.a_ne_zero _ (ReturnPrefix.generators_ne_zero F E hF) n (congrArg Subtype.val h)

theorem a_limit_valuation (hF : ∀ j, F j ≠ 0)
    (hconst : ∀ j, (F j).coeff 0 ≠ 0) (n : ℕ) :
    valuations (Set.range F) d .limit (ReturnPrefix.a (generators F E) n) = exp (-1 : ℤ) := by
  have hX : HorizontalOrders.Retained (Set.range F) HorizontalOrders.xPoint := by
    apply HorizontalOrders.retained_xPoint_of_constantCoeff_ne_zero
    rintro q ⟨j, rfl⟩
    exact hconst j
  change HorizontalOrders.valuation HorizontalOrders.xPoint _ = _
  rw [a_valuation_eq_X _ _ (generators_horizontal_valuation F E hF _ hX),
    HorizontalOrders.valuation_xPoint_X]

include hG hguards in
theorem a_outside_valuation (hF : ∀ j, F j ≠ 0) (n : ℕ) (i : Outside (Set.range F)) :
    valuations (Set.range F) d (.outside i) (ReturnPrefix.a (generators F E) n) = 1 := by
  rcases i with p | p
  · exact a_guard F E d hG hguards n p
  · change HorizontalOrders.valuation p.val _ = _
    rw [a_valuation_eq_X _ _ (generators_horizontal_valuation F E hF _ p.property.1)]
    have h := HorizontalOrders.valuation_factor_of_ne p.val HorizontalOrders.xPoint
      (Ne.symm p.property.2)
    simpa only [PrincipalProfiles.factor, HorizontalOrders.xPoint, RatFunc.algebraMap_X] using h

end Actual

section Irreducible

variable (F : ℕ → ℚ[X]) (hF : ∀ i, (F i).Monic ∧ Irreducible (F i))
  (hinj : Function.Injective F) (hconst : ∀ i, (F i).coeff 0 ≠ 0)
  (E : ℕ → ℕ) (d : PairedDomain.Places) (hG : GeneratorProfiles F E d)
  (hfirst : (d.primary 0).val.valuation = 2) (hguards : ∀ p, IsUnit (d.guard p))
  (hguard : ∀ x : RatFunc ℚ, x ≠ 0 →
    {p : PrimeIndex | PairedDomain.vertical d (.inr p) x ≠ 1}.Finite)

theorem aElement_primary (n j : ℕ) :
    ((profiles F hF hinj hconst E d hG hguard).value (.primary j)
      (aElement F E d hG hfirst hguards n) : ℤ) = primaryAtomProfile n j := by
  rw [profiles_value_cast F hF hinj hconst E d hG hguard _ _
    (aElement_ne_zero F E d hG hfirst hguards (fun j => (hF j).1.ne_zero) n)]
  change -log (PairedDomain.vertical d (.inl j) (ReturnPrefix.a (generators F E) n)) = _
  rw [a_primary F E d hG hfirst, log_exp, neg_neg]

theorem aElement_limit (n : ℕ) :
    (profiles F hF hinj hconst E d hG hguard).value .limit
      (aElement F E d hG hfirst hguards n) = 1 := by
  change (-log (valuations (Set.range F) d .limit (ReturnPrefix.a (generators F E) n))).toNat = 1
  rw [a_limit_valuation F E d (fun j => (hF j).1.ne_zero) hconst, log_exp]
  rfl

theorem aElement_outside (n : ℕ) (i : Outside (Set.range F)) :
    (profiles F hF hinj hconst E d hG hguard).value (.outside i)
      (aElement F E d hG hfirst hguards n) = 0 := by
  change (-log (valuations (Set.range F) d (.outside i) (ReturnPrefix.a (generators F E) n))).toNat = 0
  rw [a_outside_valuation F E d hG hguards (fun j => (hF j).1.ne_zero), log_one]
  rfl

include hF hinj hconst hguard in
/-- Every term of the actual return sequence, including t=a₀, is an atom. -/
theorem aElement_irreducible (n : ℕ) : Irreducible (aElement F E d hG hfirst hguards n) :=
  ValuationProfiles.irreducible_of_primaryAtomProfile
    (profiles F hF hinj hconst E d hG hguard)
    (aElement_ne_zero F E d hG hfirst hguards (fun j => (hF j).1.ne_zero) n) n
    (aElement_limit F hF hinj hconst E d hG hfirst hguards hguard n)
    (aElement_outside F hF hinj hconst E d hG hfirst hguards hguard n)
    (aElement_primary F hF hinj hconst E d hG hfirst hguards hguard n)

end Irreducible

end UnconditionalCounterexample.AtomProfiles
