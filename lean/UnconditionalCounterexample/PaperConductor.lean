import UnconditionalCounterexample.PaperLocalConductor
import UnconditionalCounterexample.PaperGenericRecovery

/-!
# The paired local conductor for every subring with unbounded lengths

For the single PaperConstruction.domain, an element with unbounded intrinsic
nonunit decomposition lengths supplies the actual escaping bounded listed
sequence. The concrete local conductor application then has no remaining
construction, profile, word-extraction, local-estimate or conductor hypotheses.
-/

namespace UnconditionalCounterexample.PaperConductor

open Polynomial PrimaryChoices

theorem conductor_eq_pair_of_unbounded (T : Subring PaperConstruction.domain)
    (x : T) (hx : x ≠ 0) (hunbounded : ¬ Factorization.HasBoundedFactorizations x)
    (j : ℕ) :
    RadicalConductor.conductorIdeal (PaperLocalConductor.localImage j T) = Ideal.span
      {algebraMap ℚ_[(primes j).val][X]
        (PoleAlgebra.generated (ScalarExtension.extendedSet ℚ ℚ_[(primes j).val] PaperConstruction.poles))
        ((X - C (SequenceLocalTransfer.branch PaperConstruction.construction j false)) *
          (X - C (SequenceLocalTransfer.branch PaperConstruction.construction j true)))} := by
  obtain ⟨r, _, y, stage, w, _, hstage, hbound, _, hword⟩ :=
    PaperGenericRecovery.exists_listed_sequence_of_unbounded T x hx hunbounded
  exact PaperLocalConductor.conductor_eq_pair_of_listed_sequence T y stage hstage w
    (2 * r) hbound hword j

end UnconditionalCounterexample.PaperConductor
