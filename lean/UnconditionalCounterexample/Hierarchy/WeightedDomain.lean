import UnconditionalCounterexample.Hierarchy.WeightedDomainBase
import UnconditionalCounterexample.Hierarchy.WeightedAtoms
import UnconditionalCounterexample.Hierarchy.IntegerValued
import UnconditionalCounterexample.Hierarchy.EvaluationStalks
import UnconditionalCounterexample.Hierarchy.OverringStalks

/-! # The ambient overring and its rational prime atoms -/

noncomputable section
namespace UnconditionalCounterexample.Hierarchy.Weighted

open Polynomial GuardSupport DiscreteOrders WithZero

local instance weightedDomainRatAlgebra : Algebra ℚ (RatFunc ℚ) := RatFunc.instAlgebraOfPolynomial ℚ ℚ

variable (P : ℕ → FiberPlace) (S : Set ℚ[X])

def fibers (q : PrimeIndex) : Set ℤ_[q.val] :=
  {z | (∃ (n : ℕ) (x : Fiber) (h : (P n).prime = q), (h ▸ (P n).emb x) = z) ∨
    (q ∉ Set.range (fun n => (P n).prime) ∧ z = PaperConstruction.places.guard q)}

theorem fibers_selected (hi : Function.Injective (fun n => (P n).prime)) (n : ℕ) :
    fibers P (P n).prime = Set.range (P n).emb := by
  ext z
  constructor
  · rintro (⟨k,x,h,hx⟩ | ⟨h,_⟩)
    · obtain rfl := hi h
      exact ⟨x,hx⟩
    · exact False.elim (h ⟨n,rfl⟩)
  · rintro ⟨x,rfl⟩
    exact Or.inl ⟨n,x,rfl,rfl⟩

theorem fibers_guard (q : Guard P) : fibers P q.val = {PaperConstruction.places.guard q.val} := by
  ext z
  constructor
  · rintro (⟨n,_,h,_⟩ | ⟨_,h⟩)
    · exact False.elim (q.property ⟨n,h⟩)
    · exact h
  · exact fun h => Or.inr ⟨q.property,h⟩

theorem evaluation_le : evaluationRing (fibers P) ≤ ring P S := by
  intro z hz
  obtain ⟨f,rfl,h⟩ := (mem_evaluationRing_iff _ _).mp hz
  apply (IntersectionDomain.mem_intersection _ _ _).mpr
  refine ⟨PoleAlgebra.polynomial_mem _ f, ?_⟩
  have hu (q : PrimeIndex) (a : ℤ_[q.val]) (ha : a ∈ fibers P q) (ht : Transcendental ℚ a.val) :
      EvaluationDVR.evaluationValuation q.val a.val ht (algebraMap ℚ[X] (RatFunc ℚ) f) ≤ 1 := by
    apply (EvaluationDVR.mem_valuationSubring _ _ _).mpr
    change ‖LocalEvaluation.evalAt a.val ht (algebraMap ℚ[X] (RatFunc ℚ) f)‖ ≤ 1
    rw [LocalEvaluation.evalAt_apply, RatFunc.num_algebraMap, RatFunc.denom_algebraMap, map_one, div_one]
    exact h q a ha
  rintro (⟨n,x⟩ | q)
  · apply hu (P n).prime ((P n).emb x)
    exact Or.inl ⟨n,x,rfl,rfl⟩
  · apply hu q.val (PaperConstruction.places.guard q.val)
    exact Or.inr ⟨q.property,rfl⟩

theorem intZ_le : intZInK ≤ ring P S := by
  rintro z ⟨f,hf,rfl⟩
  apply evaluation_le P S
  exact (mem_evaluationRing_iff _ _).mpr ⟨f,rfl,fun q a _ => norm_eval₂_le_one_of_integerValued q.val f hf a⟩

theorem fractionRing : IsFractionRing (ring P S) (RatFunc ℚ) :=
  RationalFunctionSubring.isFractionRing_of_X_mem _ (evaluation_le P S (X_mem_evaluationRing _))

theorem not_isField : ¬ IsField (ring P S) := by
  intro h
  let q := (P 0).prime
  have hn : (q.val : ring P S) ≠ 0 := Nat.cast_ne_zero.mpr q.property.ne_zero
  have hu : IsUnit (q.val : ring P S) := isUnit_iff_exists_inv.mpr (h.mul_inv_cancel hn)
  have hz := order_unit_on_ring (PoleAlgebra.generated S).toSubring (valuation P) _ hu (.inl (0,mark false))
  change order (valuation P (.inl (0,mark false))) (q.val : RatFunc ℚ) = 0 at hz
  simp [order_prime, placePrime, q] at hz

theorem isAlmostDedekind (hi : Function.Injective (fun n => (P n).prime)) :
    IsAlmostDedekindDomain (ring P S) := by
  let := evaluationRing_fractionRing (fibers P)
  apply almostDedekind_overring _ _ (evaluation_le P S) _ (not_isField P S)
  apply evaluationRing_isAlmostDedekind
  · intro q
    by_cases h : q ∈ Set.range (fun n => (P n).prime)
    · obtain ⟨n,rfl⟩ := h
      rw [fibers_selected P hi]
      exact isCompact_range (P n).continuous
    · rw [fibers_guard P ⟨q,h⟩]
      exact isCompact_singleton
  · intro q
    by_cases h : q ∈ Set.range (fun n => (P n).prime)
    · obtain ⟨n,rfl⟩ := h
      exact ⟨_,Or.inl ⟨n,mark false,rfl,rfl⟩⟩
    · exact ⟨_,Or.inr ⟨h,rfl⟩⟩
  · rintro q a (⟨n,x,rfl,rfl⟩ | ⟨_,rfl⟩)
    · exact (P n).transcendental x
    · exact PaperConstruction.places.guard_trans _

/-- Every rational prime is an atom if pole units have constant parity on each selected fiber. -/
theorem prime_irreducible (hi : Function.Injective (fun n => (P n).prime))
    (hpar : ∀ (b : ring P S), IsUnit (IntersectionDomain.inclusion _ (valuation P) b) →
      ∀ n x y, order (valuation P (.inl (n,x))) (b : RatFunc ℚ) % 2 =
        order (valuation P (.inl (n,y))) (b : RatFunc ℚ) % 2)
    (q : PrimeIndex) : Irreducible (q.val : ring P S) := by
  classical
  let C := {i : Places P | placePrime P i = q}
  have hB : IsUnit (q.val : PoleAlgebra.generated S) := by
    have hq : (q.val : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr q.property.ne_zero
    simpa using (isUnit_iff_ne_zero.mpr hq).map (algebraMap ℚ (PoleAlgebra.generated S))
  apply irreducible_of_fiber_parity (PoleAlgebra.generated S).toSubring (valuation P) _ hB C
  · by_cases h : q ∈ Set.range (fun n => (P n).prime)
    · obtain ⟨n,hn⟩ := h
      exact ⟨.inl (n,mark false),hn⟩
    · exact ⟨.inr ⟨q,h⟩,rfl⟩
  · exact fun i => order_prime P i q
  · intro b hb i hi' j hj
    change placePrime P i = q at hi'
    change placePrime P j = q at hj
    rcases i with ⟨n,x⟩ | g <;> rcases j with ⟨m,y⟩ | k
    · obtain rfl := hi (hi'.trans hj.symm)
      exact hpar b hb n x y
    · exact False.elim (k.property ⟨n,hi'.trans hj.symm⟩)
    · exact False.elim (g.property ⟨m,hj.trans hi'.symm⟩)
    · obtain rfl : g = k := Subtype.ext (hi'.trans hj.symm)
      rfl

end UnconditionalCounterexample.Hierarchy.Weighted
