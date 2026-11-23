import UnconditionalCounterexample.Variations.DyadicPrefixAgreement
import UnconditionalCounterexample.Variations.DyadicScheduledProof

/-! # Permanent profiles of the two factors prepared at a split opening -/

noncomputable section
namespace UnconditionalCounterexample.Variations.DyadicLedger.ScheduledSplit
open GuardSupport Univariate Calibrated DyadicDeviations

/-- On the actual calibrated run the computed split transports both the
coordinate inequalities and the reserved raw's signed product identity. -/
theorem profiled (r : ℕ) (hx : (taskAt r).element ≠ 0) (w : PreparedAt r hx) : Profiled r hx w := by
  let E := prefixEmbedding policy (stage r)
  let I := w.instruction (taskAt r)
  let x := Units.mk0 (taskAt r).element hx
  have htask := extend_prefix_signed policy (stage r) x (task_exterior policy r hx)
  have hpos : 0 < stage r := run.opening_strict (Nat.zero_lt_succ r)
  have hcoarse := extend_prefix_signed policy (stage r) I.coarse (coarse_exterior policy (stage r) hpos w.left)
  refine ⟨E.profile w.left,E.profile w.right,?_,?_⟩
  · rw [← htask]
    exact extend_split policy (stage r) w.split
  · rw [← hcoarse]
    exact (extend_word policy (stage r) (oldSigned policy (stage r) I.coarse) w.exponents w.basis).trans
      (congrArg E.profile w.word)

end UnconditionalCounterexample.Variations.DyadicLedger.ScheduledSplit
