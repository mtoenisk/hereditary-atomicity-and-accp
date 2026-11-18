import UnconditionalCounterexample

/-- One hereditarily atomic domain fails ACCP, and the same domain's subrings
fail ACCP exactly when their additive index is finite. -/
example : ∃ D : Subring (RatFunc ℚ),
    Factorization.IsHereditarilyAtomic D ∧ ¬ WfDvdMonoid D ∧
      ∀ T : Subring D, ¬ WfDvdMonoid T ↔ Finite (D ⧸ T.toAddSubgroup) := by
  obtain ⟨D, hA, hB⟩ := UnconditionalCounterexample.paperCounterexampleExists
  obtain ⟨hAtomic, _, _, _, hFail, _⟩ := hA
  refine ⟨D, hAtomic, hFail, ?_⟩
  intro T
  obtain ⟨hAccp, hIndex, _⟩ := hB T
  exact hAccp.trans hIndex
