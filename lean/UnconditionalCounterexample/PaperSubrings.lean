import UnconditionalCounterexample.PaperAtomicity
import UnconditionalCounterexample.PaperChainHeight

/-!
# Theorem B for the single constructed domain

Every unital subring is classified by its actual additive index. The integer
conductor theorem and finite-residue chains identify failure of BF and ACCP
with finite index; every subring of an infinite-index subring is BF. The same
hereditary atomicity theorem removes the last atomicity premise from the
high-order unbounded-length conclusion.
-/

namespace UnconditionalCounterexample.PaperConstruction

private theorem residue_primary_nonunit : ¬ IsUnit (places.primary 0) :=
  PairedResidues.not_isUnit_of_valuation_pos _ (by rw [first_primary_valuation]; decide)

private theorem residue_guard_unit (p : GuardSupport.PrimeIndex) : IsUnit (places.guard p) :=
  construction.chain.guardChain.value_unit p

theorem integer_order_index (n : ℕ) (hn : 0 < n) :
    (PaperTargets.integerOrder domain n).toAddSubgroup.index = n :=
  PairedResidues.order_index poles places n hn.ne' residue_primary_nonunit residue_guard_unit

theorem integer_order_conductor (n : ℕ) (hn : 0 < n) :
    RadicalConductor.conductorIdeal (PaperTargets.integerOrder domain n) = Ideal.span {(n : domain)} :=
  PairedResidues.order_conductor poles places n hn.ne' residue_primary_nonunit residue_guard_unit

theorem finite_quotient_iff_integer_order (T : Subring domain) :
    Finite (domain ⧸ T.toAddSubgroup) ↔
      ∃ n : ℕ, 0 < n ∧ T = PaperTargets.integerOrder domain n :=
  PairedResidues.finite_quotient_iff_order poles places residue_primary_nonunit residue_guard_unit T

/-- A larger additive subgroup has finite index when the smaller one does. -/
theorem finite_quotient_of_subring_le (S T : Subring domain) (hST : S ≤ T)
    (hS : Finite (domain ⧸ S.toAddSubgroup)) : Finite (domain ⧸ T.toAddSubgroup) := by
  apply T.toAddSubgroup.index_ne_zero_iff_finite.mp
  exact ne_zero_of_dvd_ne_zero (S.toAddSubgroup.index_ne_zero_iff_finite.mpr hS)
    (AddSubgroup.index_dvd_of_le (show S.toAddSubgroup ≤ T.toAddSubgroup from hST))

theorem finite_quotient_of_integer_conductor (T : Subring domain) (n : ℕ) (hn : 0 < n)
    (hconductor : ∀ z : domain, (n : domain)*z ∈ T) : Finite (domain ⧸ T.toAddSubgroup) := by
  apply finite_quotient_of_subring_le (PaperTargets.integerOrder domain n) T ?_
    ((finite_quotient_iff_integer_order _).mpr ⟨n,hn,rfl⟩)
  rintro x ⟨z,y,rfl⟩
  exact T.add_mem (intCast_mem T z) (hconductor y)

/-- The actual integer-conductor theorem and actual high-order chains meet at finite index. -/
theorem nonBF_iff_finite_quotient (T : Subring domain) :
    ¬ Factorization.IsBFDomain T ↔ Finite (domain ⧸ T.toAddSubgroup) := by
  constructor
  · intro hT
    obtain ⟨n,hn,hconductor⟩ := PaperIntegerConductor.exists_integer_conductor T hT
    exact finite_quotient_of_integer_conductor T n hn hconductor
  · exact finite_index_not_isBFDomain T

theorem nonACCP_iff_nonBF (T : Subring domain) :
    ¬ WfDvdMonoid T ↔ ¬ Factorization.IsBFDomain T := by
  constructor
  · intro hACCP hBF
    exact hACCP hBF.wfDvdMonoid
  · intro hBF
    exact finite_index_not_wfDvdMonoid T ((nonBF_iff_finite_quotient T).mp hBF)

/-- Every unital subring of an infinite-index subring is itself BF. -/
theorem infinite_quotient_hereditarilyBF (T : Subring domain)
    (hInfinite : Infinite (domain ⧸ T.toAddSubgroup)) : Factorization.IsHereditarilyBF T := by
  let : Infinite (domain ⧸ T.toAddSubgroup) := hInfinite
  intro S
  apply (Factorization.subring_map_isBFDomain_iff S T.subtype Subtype.val_injective).mp
  by_contra hS
  have hf := (nonBF_iff_finite_quotient (S.map T.subtype)).mp hS
  have hle : S.map T.subtype ≤ T := by
    rintro z ⟨y,_,rfl⟩
    exact y.property
  have hfinite := finite_quotient_of_subring_le _ T hle hf
  let : Finite (domain ⧸ T.toAddSubgroup) := hfinite
  exact not_finite (domain ⧸ T.toAddSubgroup)

/-- The unbounded atomic-length assertion in Proposition 7.4, now with no atomicity premise. -/
theorem finite_index_atom_lengths_unbounded
    (T : Subring domain) (hfinite : Finite (domain ⧸ T.toAddSubgroup))
    (x : T) (hx : x ≠ 0)
    (horder : 2 ≤ PrimaryStabilization.tOrder ((x : domain) : RatFunc ℚ)) :
    ¬ BddAbove (Factorization.factorizationLengths x) :=
  finite_index_atom_lengths_unbounded_of_atomicity T hfinite (hereditarilyAtomic T) x hx horder

/-- Every clause of the manuscript's Theorem B for every actual unital subring. -/
theorem theoremBConclusion : PaperTargets.TheoremBConclusion domain := by
  intro T
  refine ⟨nonACCP_iff_nonBF T, nonBF_iff_finite_quotient T,
    finite_quotient_iff_integer_order T, ?_, infinite_quotient_hereditarilyBF T⟩
  intro n hn hT
  subst T
  exact ⟨integer_order_index n hn, integer_order_conductor n hn⟩

end UnconditionalCounterexample.PaperConstruction
