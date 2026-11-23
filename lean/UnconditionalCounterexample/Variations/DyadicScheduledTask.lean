import UnconditionalCounterexample.Variations.DyadicPrefixHistory
import UnconditionalCounterexample.Variations.DyadicPreparedCoarse

/-!
# The prepared task on the single concrete split-aware run

The finite feasibility proof is consumed by the actual opening after the
task's preparation. This identifies its installed instruction and the genuine
earlier raw-history support in the dependent recursion.
-/

noncomputable section
namespace UnconditionalCounterexample.Variations.DyadicLedger.ScheduledSplit
open GuardSupport Univariate RecursivePrefix Calibrated PrefixInstruction DiscreteOrders

abbrev run := driver PrefixInstruction.policy
abbrev stage (r : ℕ) := run.opening (r+1)
abbrev memory (r : ℕ) := run.state (stage r)
abbrev previous (r : ℕ) := (chain run.requirements).approx (stage r)
abbrev sites (r : ℕ) := table run.requirements (stage r)
abbrev aux (r : ℕ) := OpeningCalibration.columns (phase (memory r) (previous r) (sites r))

abbrev PreparedAt (r : ℕ) (hx : (taskAt r).element ≠ 0) :=
  Prepared (memory r) (previous r) (sites r) (aux r) (Units.mk0 _ hx)

theorem named (x : RatFunc ℚ) {m : ℕ} (hm : 0 < m) :
    ∃ r, (taskAt r).element = x ∧ (taskAt r).modulus = m := by
  obtain ⟨r,he⟩ := FreezingCalendar.splitAt_surjective (x,⟨m,hm⟩)
  exact ⟨r,congrArg Prod.fst he,congrArg (fun t => t.2.val) he⟩

/-- The actual layout and saved instruction selected by the concrete policy
at the opening handling a named, feasible split. -/
theorem installs (r : ℕ) (hx : (taskAt r).element ≠ 0) (hp : Nonempty (PreparedAt r hx)) :
    ∃ w : PreparedAt r hx, actualLayout PrefixInstruction.policy (stage r) = w.layout (taskAt r) ∧
      (openingData (planner PrefixInstruction.policy) (r+1)).instruction = some (w.instruction (taskAt r)) := by
  let m := memory r
  have hr : m.rounds = r+1 := run.opening_rounds (r+1)
  have hpos : m.rounds ≠ 0 := by omega
  have he : m.rounds - 1 = r := by omega
  have choose (task : SplitTask) (ht : taskAt (m.rounds-1) = task) (hne : task.element ≠ 0)
      (hprep : Nonempty (Prepared m (previous r) (sites r) (aux r) (Units.mk0 _ hne))) :
      ∃ w : Prepared m (previous r) (sites r) (aux r) (Units.mk0 _ hne),
        PrefixInstruction.policy m (previous r) (sites r) (aux r) = w.layout task := by
    subst task
    exact policy_selects _ _ _ hpos hne hprep
  have hw := choose (taskAt r) (congrArg taskAt he) hx hp
  obtain ⟨w,hw⟩ := hw
  have hl : actualLayout PrefixInstruction.policy (stage r) = w.layout (taskAt r) := hw
  refine ⟨w,hl,?_⟩
  change (actualLayout PrefixInstruction.policy (stage r)).instruction = _
  rw [hl]
  rfl

theorem precedes (r : ℕ) (hx : (taskAt r).element ≠ 0) (w : PreparedAt r hx)
    (h : actualLayout PrefixInstruction.policy (stage r) = w.layout (taskAt r)) :
    w.exponents.support ⊆ (Finset.range (run.opening (r+1+1)-1+1)).image
      (fun j => (run.actualRequest j).column) := by
  apply prefix_coefficients_emitted PrefixInstruction.policy (r+1) (Units.mk0 _ hx) (aux r) w
  exact congrArg Layout.block h

theorem modulus_roles (r : ℕ) (hx : (taskAt r).element ≠ 0) (w : PreparedAt r hx)
    (p : PrimeIndex) (hp : p.val ∣ (w.instruction (taskAt r)).task.modulus) :
    (w.instruction (taskAt r)).first p.val =
        (run.permanentRole p).elim true (fun q => !q.channel) ∧
      ∀ c k j, run.permanentRole p = some (.regular c k j) → j < (w.instruction (taskAt r)).index :=
  previous_modulus_data (planner PrefixInstruction.policy) r (aux r)
    (source (memory r) (previous r) (sites r) (Units.mk0 _ hx)).natRegular.cutoff p hp

end UnconditionalCounterexample.Variations.DyadicLedger.ScheduledSplit
