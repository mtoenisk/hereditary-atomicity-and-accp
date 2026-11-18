import UnconditionalCounterexample.PaperSubrings

noncomputable section
namespace UnconditionalCounterexample.PaperConstruction

private theorem primary_nonunit : ¬ IsUnit (places.primary 0) :=
  PairedResidues.not_isUnit_of_valuation_pos _ (by rw [first_primary_valuation]; decide)

private theorem guard_unit (p : GuardSupport.PrimeIndex) : IsUnit (places.guard p) :=
  construction.chain.guardChain.value_unit p

/-- The actual additive quotient by Z+nD is ZMod n. -/
def integerOrderQuotientEquiv (n : ℕ) (hn : 0 < n) :
    (domain ⧸ (PaperTargets.integerOrder domain n).toAddSubgroup) ≃+ ZMod n :=
  PairedResidues.orderQuotientEquiv poles places n hn.ne' primary_nonunit guard_unit

/-- In Proposition 7.3 the generator is the literal t=X in the constructed domain. -/
theorem integer_order_quotient_generated_by_parameter (n : ℕ) (hn : 0 < n) :
    ∀ x : domain ⧸ (PaperTargets.integerOrder domain n).toAddSubgroup,
      ∃ z : ℤ, z • QuotientAddGroup.mk'
        (PaperTargets.integerOrder domain n).toAddSubgroup parameter = x :=
  PairedResidues.orderQuotient_generated_by_X poles places n hn.ne' primary_nonunit guard_unit

/-- A finite-index unital subring containing t is all of D. -/
theorem eq_top_of_finite_index_of_parameter_mem (T : Subring domain)
    (hfinite : Finite (domain ⧸ T.toAddSubgroup)) (ht : parameter ∈ T) : T = ⊤ := by
  obtain ⟨n,hn,rfl⟩ := (finite_quotient_iff_integer_order T).mp hfinite
  apply top_unique
  intro x _
  obtain ⟨z,hz⟩ := integer_order_quotient_generated_by_parameter n hn
    (QuotientAddGroup.mk' (PaperTargets.integerOrder domain n).toAddSubgroup x)
  have htzero : QuotientAddGroup.mk' (PaperTargets.integerOrder domain n).toAddSubgroup parameter = 0 :=
    (QuotientAddGroup.eq_zero_iff parameter).mpr ht
  have hxzero : QuotientAddGroup.mk' (PaperTargets.integerOrder domain n).toAddSubgroup x = 0 := by
    rw [htzero, zsmul_zero] at hz
    exact hz.symm
  exact (QuotientAddGroup.eq_zero_iff x).mp hxzero

/-- Every proper unital subring containing t has infinite additive index. -/
theorem infinite_quotient_of_parameter_mem (T : Subring domain) (hproper : T ≠ ⊤)
    (ht : parameter ∈ T) : Infinite (domain ⧸ T.toAddSubgroup) := by
  apply not_finite_iff_infinite.mp
  intro hfinite
  exact hproper (eq_top_of_finite_index_of_parameter_mem T hfinite ht)

/-- The manuscript's proper-subring corollary, hereditary over all further unital subrings. -/
theorem proper_subring_containing_parameter_hereditarilyBF (T : Subring domain)
    (hproper : T ≠ ⊤) (ht : parameter ∈ T) : Factorization.IsHereditarilyBF T :=
  infinite_quotient_hereditarilyBF T (infinite_quotient_of_parameter_mem T hproper ht)

end UnconditionalCounterexample.PaperConstruction
