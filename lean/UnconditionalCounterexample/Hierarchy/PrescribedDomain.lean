import UnconditionalCounterexample.Hierarchy.PrescribedFiber
import UnconditionalCounterexample.Hierarchy.PrescribedGuards
import UnconditionalCounterexample.Hierarchy.PrescribedRank
import UnconditionalCounterexample.Hierarchy.IntegerValued
import UnconditionalCounterexample.Hierarchy.EvaluationRing
import UnconditionalCounterexample.Hierarchy.EvaluationStalks
import UnconditionalCounterexample.Hierarchy.OverringStalks

/-! # Prescribed-length rings in the rational function field -/

noncomputable section
namespace UnconditionalCounterexample.Hierarchy.Prescribed

open Polynomial GuardSupport Set WithZero

local instance : Algebra ℚ (RatFunc ℚ) := RatFunc.instAlgebraOfPolynomial ℚ ℚ

variable (m : ℕ → ℕ) (p : PrimeIndex)

/-- The compact product of the designated finite rows in the p-adic integers. -/
def point : RowPoint m → ℤ_[p.val] :=
  (exists_rows_in_ball m p.val 0 1 one_pos).choose

theorem point_embedding : Topology.IsClosedEmbedding (point m p) :=
  (exists_rows_in_ball m p.val 0 1 one_pos).choose_spec.1

theorem point_transcendental (x : RowPoint m) : Transcendental ℚ (point m p x).val :=
  ((exists_rows_in_ball m p.val 0 1 one_pos).choose_spec.2 x).2

abbrev rowVal (x : RowPoint m) : Valuation (RatFunc ℚ) ℤᵐ⁰ :=
  EvaluationDVR.evaluationValuation p.val (point m p x).val (point_transcendental m p x)

/-- Keep the original construction's finite-character guard at each other prime. -/
def fibers : EvaluationFibers :=
  Function.update (fun q : PrimeIndex => {PaperConstruction.places.guard q}) p (range (point m p))

@[simp] theorem fibers_distinguished : fibers m p p = range (point m p) :=
  Function.update_self ..

theorem fibers_other {q : PrimeIndex} (hq : q ≠ p) :
    fibers m p q = {PaperConstruction.places.guard q} := Function.update_of_ne hq ..

theorem fibers_compact (q : PrimeIndex) : IsCompact (fibers m p q) := by
  by_cases h : q = p
  · subst q
    rw [fibers_distinguished]
    exact isCompact_range (point_embedding m p).continuous
  · rw [fibers_other m p h]
    exact isCompact_singleton

theorem fibers_nonempty (q : PrimeIndex) : (fibers m p q).Nonempty := by
  by_cases h : q = p
  · subst q
    rw [fibers_distinguished]
    exact range_nonempty _
  · rw [fibers_other m p h]
    exact singleton_nonempty _

theorem fibers_transcendental (q : PrimeIndex) (z : ℤ_[q.val]) (hz : z ∈ fibers m p q) :
    Transcendental ℚ z.val := by
  by_cases h : q = p
  · subst q
    rw [fibers_distinguished] at hz
    obtain ⟨x, rfl⟩ := hz
    exact point_transcendental m p x
  · rw [fibers_other m p h] at hz
    exact (mem_singleton_iff.mp hz) ▸ PaperConstruction.places.guard_trans q

/-- Intersect a specified polynomial pole algebra with the compact selected
fiber at p and the single guard at every other prime. -/
def ring (S : Set ℚ[X]) : Subring (RatFunc ℚ) :=
  IntersectionDomain.intersection (PoleAlgebra.generated S).toSubring
    (Sum.elim (rowVal m p) (fun q : {q : PrimeIndex // q ≠ p} => guardVal q.val))

theorem mem_ring_iff (S : Set ℚ[X]) (f : RatFunc ℚ) :
    f ∈ ring m p S ↔ f ∈ PoleAlgebra.generated S ∧
      (∀ x, rowVal m p x f ≤ 1) ∧ ∀ q : PrimeIndex, q ≠ p → guardVal q f ≤ 1 := by
  rw [ring, IntersectionDomain.mem_intersection]
  constructor
  · rintro ⟨hf, h⟩
    exact ⟨hf, fun x => h (.inl x), fun q hq => h (.inr ⟨q, hq⟩)⟩
  · rintro ⟨hf, hx, hq⟩
    refine ⟨hf, ?_⟩
    rintro (x | q)
    · exact hx x
    · exact hq q.val q.property

/-- The literal inclusion of the prescribed ring into its pole algebra. -/
def ringSubtype (S : Set ℚ[X]) : ring m p S →+* PoleAlgebra.generated S :=
  IntersectionDomain.inclusion _ _

theorem evaluationRing_le_ring (S : Set ℚ[X]) : evaluationRing (fibers m p) ≤ ring m p S := by
  intro z hz
  obtain ⟨f, rfl, hf⟩ := (mem_evaluationRing_iff _ _).mp hz
  apply (mem_ring_iff ..).mpr
  have h (q : PrimeIndex) (a : ℤ_[q.val]) (ha : a ∈ fibers m p q) :
      EvaluationDVR.evaluationValuation q.val a.val (fibers_transcendental m p q a ha)
        (algebraMap ℚ[X] (RatFunc ℚ) f) ≤ 1 := by
    apply (EvaluationDVR.mem_valuationSubring q.val _ _).mpr
    change ‖LocalEvaluation.evalAt a.val _ (algebraMap ℚ[X] (RatFunc ℚ) f)‖ ≤ 1
    rw [LocalEvaluation.evalAt_apply, RatFunc.num_algebraMap, RatFunc.denom_algebraMap, map_one, div_one]
    exact hf q a ha
  refine ⟨PoleAlgebra.polynomial_mem S f, fun x => h p _ (by simp), fun q hq => ?_⟩
  exact h q _ (by rw [fibers_other m p hq]; exact mem_singleton _)

theorem intZ_le_ring (S : Set ℚ[X]) : intZInK ≤ ring m p S := by
  rintro z ⟨f, hf, rfl⟩
  exact (mem_ring_iff ..).mpr ⟨PoleAlgebra.polynomial_mem S f,
    fun x => integerValued_eval_integral _ f hf _ (point_transcendental m p x),
    fun q _ => integerValued_eval_integral _ f hf _ (PaperConstruction.places.guard_trans q)⟩

theorem ring_fractionRing (S : Set ℚ[X]) : IsFractionRing (ring m p S) (RatFunc ℚ) :=
  RationalFunctionSubring.isFractionRing_of_X_mem _ (evaluationRing_le_ring m p S (X_mem_evaluationRing _))

theorem ring_not_field (S : Set ℚ[X]) : ¬ IsField (ring m p S) := by
  intro h
  have hp : (p.val : ring m p S) ≠ 0 := Nat.cast_ne_zero.mpr p.property.ne_zero
  obtain ⟨b, hb⟩ := h.mul_inv_cancel hp
  have he : (p.val : RatFunc ℚ) * b = 1 := congrArg (ring m p S).subtype hb
  have hmem := ((mem_ring_iff m p S b).mp b.property).2.1 (fun _ => 0)
  rw [eq_inv_of_mul_eq_one_right he] at hmem
  change EvaluationDVR.valuation p.val _ ((p.val : RatFunc ℚ)⁻¹) ≤ 1 at hmem
  rw [map_inv₀, EvaluationDVR.valuation_prime] at hmem
  exact (by decide : ¬ (exp (-1 : ℤ))⁻¹ ≤ 1) hmem

theorem ring_isAlmostDedekind (S : Set ℚ[X]) : IsAlmostDedekindDomain (ring m p S) := by
  let := evaluationRing_fractionRing (fibers m p)
  exact almostDedekind_overring _ _ (evaluationRing_le_ring m p S)
    (evaluationRing_isAlmostDedekind _ (fibers_compact m p) (fibers_nonempty m p)
      (fibers_transcendental m p)) (ring_not_field m p S)

end UnconditionalCounterexample.Hierarchy.Prescribed
