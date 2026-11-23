import UnconditionalCounterexample.EvaluationChoices
import Mathlib.Topology.MetricSpace.Perfect
import Mathlib.Topology.Algebra.Module.PerfectSpace
import Mathlib.Logic.Equiv.Nat

/-! # Compact transcendental fibers in a prescribed p-adic ball -/

noncomputable section
namespace UnconditionalCounterexample.Hierarchy.Prescribed

open Set Function

private theorem exists_stream_outside {s : Set (ℕ → Bool)} (hs : s.Countable) :
    ∃ x, x ∉ s := by
  by_contra! h
  have hu : s = univ := eq_univ_of_forall h
  obtain ⟨f, hf⟩ := hs.exists_eq_range (hu ▸ univ_nonempty)
  let x : ℕ → Bool := fun n => !(f n n)
  obtain ⟨n, hn⟩ : x ∈ range f := hf ▸ h x
  have heq := congrFun hn n
  change f n n = !(f n n) at heq
  cases hfn : f n n <;> simp [hfn] at heq

private def interleave (x y : ℕ → Bool) (i : ℕ) : Bool :=
  Sum.elim x y (Equiv.natSumNatEquivNat.symm i)

private theorem interleave_injective :
    Injective (fun z : (ℕ → Bool) × (ℕ → Bool) => interleave z.1 z.2) := by
  intro z w h
  apply Prod.ext
  · funext n
    simpa [interleave] using congrFun h (Equiv.natSumNatEquivNat (.inl n))
  · funext n
    simpa [interleave] using congrFun h (Equiv.natSumNatEquivNat (.inr n))

private theorem continuous_interleave (x : ℕ → Bool) : Continuous (interleave x) := by
  apply continuous_pi
  intro i
  unfold interleave
  cases Equiv.natSumNatEquivNat.symm i with
  | inl n => exact continuous_const
  | inr n => exact continuous_apply n

/-- Every ball in the p-adic integers contains a continuous copy of Cantor space
all of whose points are transcendental over the rationals. -/
theorem exists_cantor_in_ball (p : ℕ) [Fact p.Prime] (a : ℤ_[p]) (ε : ℝ) (hε : 0 < ε) :
    ∃ e : (ℕ → Bool) → ℤ_[p], Continuous e ∧ Injective e ∧
      ∀ x, e x ∈ Metric.ball a ε ∧ Transcendental ℚ (e x).val := by
  classical
  let U := Metric.ball (a : ℚ_[p]) (min ε 1)
  have hU : U.Nonempty := ⟨a, Metric.mem_ball_self (lt_min hε one_pos)⟩
  have hpU : Perfect U := ⟨IsUltrametricDist.isClosed_ball .., Metric.isOpen_ball.preperfect⟩
  obtain ⟨f, hf, hcont, hinj⟩ := hpU.exists_nat_bool_injection hU
  let pair := fun z : (ℕ → Bool) × (ℕ → Bool) => f (interleave z.1 z.2)
  have hpair : Injective pair := hinj.comp interleave_injective
  let bad := pair ⁻¹' ofPred (IsAlgebraic ℚ : ℚ_[p] → Prop)
  have hbad : bad.Countable := LocalEvaluation.algebraic_countable.preimage hpair
  obtain ⟨u, hu⟩ := exists_stream_outside (hbad.image Prod.fst)
  have hval (x : ℕ → Bool) : f (interleave u x) ∈ U := hf (mem_range_self _)
  have hint (x : ℕ → Bool) : ‖f (interleave u x)‖ ≤ 1 := by
    have hd := Metric.mem_ball.mp (hval x)
    rw [dist_eq_norm_sub] at hd
    calc
      ‖f (interleave u x)‖ = ‖(f (interleave u x) - (a : ℚ_[p])) + a‖ := by simp
      _ ≤ max ‖f (interleave u x) - a‖ ‖(a : ℚ_[p])‖ := Padic.nonarchimedean _ _
      _ ≤ 1 := max_le (hd.le.trans (min_le_right ..)) a.property
  let e : (ℕ → Bool) → ℤ_[p] := fun x => ⟨f (interleave u x), hint x⟩
  refine ⟨e, (hcont.comp (continuous_interleave u)).subtype_mk _, ?_, ?_⟩
  · intro x y heq
    exact congrArg Prod.snd (hpair (show pair (u, x) = pair (u, y) from congrArg Subtype.val heq))
  · intro x
    refine ⟨(Metric.mem_ball.mp (hval x)).trans_le (min_le_left ..), ?_⟩
    intro h
    exact hu ⟨(u, x), h, rfl⟩

private def rowBits (m : ℕ → ℕ) (x : (i : ℕ) → Fin (m i + 2)) (n : ℕ) : Bool :=
  decide ((x n.unpair.1).val = n.unpair.2)

private theorem rowBits_injective (m : ℕ → ℕ) : Injective (rowBits m) := by
  intro x y h
  funext i
  have he (z : ℕ × ℕ) : decide ((x z.1).val = z.2) = decide ((y z.1).val = z.2) := by
    let bits (v : (i : ℕ) → Fin (m i + 2)) (k : ℕ × ℕ) := decide ((v k.1).val = k.2)
    change bits x z = bits y z
    have e : bits x (Nat.unpair (Nat.pair z.1 z.2)) = bits y (Nat.unpair (Nat.pair z.1 z.2)) :=
      congrFun h _
    rwa [Nat.unpair_pair] at e
  exact Fin.ext (by simpa [eq_comm] using (he (i, (x i).val)).symm)

private theorem rowBits_continuous (m : ℕ → ℕ) : Continuous (rowBits m) := by
  apply continuous_pi
  intro n
  exact (continuous_of_discreteTopology (f := fun j : Fin (m n.unpair.1 + 2) =>
    decide (j.val = n.unpair.2))).comp (continuous_apply n.unpair.1)

/-- Independent finite coordinates of arbitrary, possibly unbounded sizes can
all be encoded in a single compact transcendental fiber. -/
theorem exists_rows_in_ball (m : ℕ → ℕ) (p : ℕ) [Fact p.Prime] (a : ℤ_[p])
    (ε : ℝ) (hε : 0 < ε) :
    ∃ e : ((i : ℕ) → Fin (m i + 2)) → ℤ_[p], Topology.IsClosedEmbedding e ∧
      ∀ x, e x ∈ Metric.ball a ε ∧ Transcendental ℚ (e x).val := by
  obtain ⟨c, hc, hi, hv⟩ := exists_cantor_in_ball p a ε hε
  exact ⟨c ∘ rowBits m, (hc.comp (rowBits_continuous m)).isClosedEmbedding
    (hi.comp (rowBits_injective m)), fun x => hv _⟩

end UnconditionalCounterexample.Hierarchy.Prescribed
