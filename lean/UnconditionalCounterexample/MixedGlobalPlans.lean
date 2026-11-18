import UnconditionalCounterexample.GlobalPlans
import UnconditionalCounterexample.MixedStageRecursion
import UnconditionalCounterexample.ConstructionRecovery

/-!
# Global plans and curve recovery for the mixed sequence

Reuse the proved prefix transport without changing any selected exponent,
denominator power, degree or test. The actual mixed sequence therefore carries
all geometric hypotheses needed to recover its rational pole algebra from
an escaping listed-word sequence. No independent geometric input is assumed.
-/

namespace UnconditionalCounterexample.MixedGlobalPlans

open Polynomial Filter RawWords ConstructionWords MixedStageRecursion RecursivePrefix GlobalPlans

variable {R : Requirements} (s : Sequence R)

/-- The actual prefix plan interpreted in the same common infinite sequence. -/
noncomputable def globalPlan (n : ℕ) : DegreePlan n s.chain.raw s.chain.exponent :=
  transportPlan (s.selection n).plan (s.chain.rawAt_agrees n) (s.chain.exponentAt_agrees n)

@[simp] theorem globalPlan_wordDen (n : ℕ) (w : Word n) :
    (globalPlan s n).wordDen w = (s.selection n).plan.wordDen w :=
  transportPlan_wordDen _ _ _ w

@[simp] theorem globalPlan_rawDen (n : ℕ) :
    (globalPlan s n).rawDen = (s.selection n).plan.rawDen :=
  transportPlan_rawDen _ _ _

@[simp] theorem globalPlan_tests (n : ℕ) :
    (globalPlan s n).tests = (s.selection n).plan.tests :=
  transportPlan_tests _ _ _

theorem globalRaw_eq_selection (n : ℕ) : s.chain.raw n = (s.selection n).raw := by
  rw [s.chain.raw_eq_selected n, s.consistent n]
  rfl

theorem globalPlan_E (n : ℕ) : (globalPlan s n).E = s.chain.exponent n := by
  rw [s.chain.exponent_eq_selected n, s.consistent n]
  rfl

theorem globalPlan_degree (n : ℕ) : (s.chain.raw n).natDegree = (globalPlan s n).degree := by
  rw [globalRaw_eq_selection]
  exact (s.selection n).raw_degree

theorem global_raw_tests (n : ℕ) : ∀ t ∈ (globalPlan s n).tests,
    t.Holds ((s.chain.raw n).map (algebraMap ℚ (AlgebraicClosure ℚ))) := by
  rw [globalPlan_tests, globalRaw_eq_selection]
  exact (s.selection n).raw_tests


/-- The same selected plans and point reservations recover the rational pole
algebra from an actual listed sequence in a mixed-construction subring. -/
theorem hull_eq_top_of_sequence
    (T : Subring (PoleAlgebra.generated (Set.range s.chain.raw)))
    (y : ℕ → T) (stage : ℕ → ℕ) (hstage : Tendsto stage atTop atTop)
    (w : ∀ i, Word (stage i))
    (hword : ∀ i, ((y i : PoleAlgebra.generated (Set.range s.chain.raw)) : RatFunc ℚ) =
      ScheduledRecovery.generators s.chain.raw s.chain.exponent (stage i) ^ (w i).latestExponent *
        (∏ j ∈ Finset.range (stage i),
          ScheduledRecovery.generators s.chain.raw s.chain.exponent j ^ (w i).oldExponent j)) :
    RationalHull.hull T = ⊤ := by
  apply ConstructionRecovery.hull_eq_top_of_coherent_plans s.chain.raw s.chain.exponent (globalPlan s)
    (globalPlan_E s) (globalPlan_degree s) s.chain.raw_irreducible
    (global_raw_tests s) 0 ?_ T y stage hstage w hword
  intro j
  simp only [eval₂_at_zero]
  exact (map_ne_zero_iff (algebraMap ℚ (AlgebraicClosure ℚ))
    (algebraMap ℚ (AlgebraicClosure ℚ)).injective).mpr (s.chain.raw_constant_ne_zero j)

end UnconditionalCounterexample.MixedGlobalPlans
