import UnconditionalCounterexample.PaperIntegerConductor
import UnconditionalCounterexample.ConstructionReturns
import UnconditionalCounterexample.ConductorFactorCounts
import UnconditionalCounterexample.FiniteDivisorBounds
import UnconditionalCounterexample.PaperSpectrum
import UnconditionalCounterexample.PaperSquareChainActual

/-!
# The unconditional hereditary atomicity counterexample

The original unital subring is arbitrary throughout. Unbounded factorizations
force an integer conductor, and the actual recurrence and its integer returns
give the late irreducible divisors used to split its elements. The same
domain has the manuscript's explicit chain starting at the square of t.
-/

namespace UnconditionalCounterexample.PaperConstruction

theorem late_return (m : ℕ) (hm : 0 < m) (N : ℕ) :
    ∃ n ≥ N, (m : domain) ∣ atom n - 1 := by
  obtain ⟨k, hk⟩ := Filter.eventually_atTop.mp
    (ConstructionReturns.eventually_integer_dvd_atom_sub_one m hm)
  exact ⟨max N k, le_max_left _ _, hk _ (le_max_right _ _)⟩

/-- Manuscript Proposition 7.2, hereditary atomicity of the constructed D. -/
theorem hereditarilyAtomic : Factorization.IsHereditarilyAtomic domain :=
  hereditarilyAtomic_of_integerConductors (fun z hz => (isUnit_iff_sign z).mp hz)
    (valuationProfiles.value .limit) (valuationProfiles.value_mul .limit)
    (fun z hz horder => FiniteDivisorBounds.hasBoundedFactorizations_of_finite_divisor_classes hz
      (finite_associates_divisors_of_order_le_one z hz (by
        rw [← valuationProfiles_limit_cast z hz]
        exact_mod_cast horder)))
    atom atom_limit
    (fun z hz hhigh => valuationProfiles.eventually_dvd_of_primaryAtomProfiles
      coordinate_divisibility atom atom_ne_zero atom_limit atom_outside atom_primary hz hhigh)
    late_return PaperIntegerConductor.exists_integer_conductor

/-- In every atom factorization in a conductor-containing subring, the number
of order-one factors is the order at t=0 and all other factors have order zero. -/
theorem factor_count (T : Subring domain) (m : ℕ) (hm : 0 < m)
    (hc : ∀ z : domain, (m : domain) * z ∈ T) {x : T} (hx : x ≠ 0)
    (L : Multiset T) (hatoms : ∀ z ∈ L, Irreducible z) (hprod : Associated L.prod x) :
    (L.filter (fun z : T => valuationProfiles.value .limit (z : domain) = 1)).card =
      valuationProfiles.value .limit (x : domain) ∧
      ∀ z ∈ L, valuationProfiles.value .limit (z : domain) ≠ 1 →
        valuationProfiles.value .limit (z : domain) = 0 :=
  valuationProfiles.factor_count_of_integer_conductor coordinate_divisibility atom atom_ne_zero
    atom_limit atom_outside atom_primary T m hc (late_return m hm) hx L hatoms hprod

theorem parameter_irreducible : Irreducible parameter := atom_irreducible 0

/-- One unconditional witness to the conjecture's failure, with the paper's
actual coordinate, chain and ratio-independence assertion. -/
theorem exists_hereditarilyAtomic_not_ACCP :
    ∃ D : Subring (RatFunc ℚ), Factorization.IsHereditarilyAtomic D ∧ ¬ WfDvdMonoid D ∧
      IsFractionRing D (RatFunc ℚ) ∧ IsAlmostDedekindDomain D ∧
      ∃ t : D, (t : RatFunc ℚ) = RatFunc.X ∧ Irreducible t ∧
        PaperTargets.SquareChainConclusion D t :=
  ⟨domain, hereditarilyAtomic, not_wfDvdMonoid, fractionRing, isAlmostDedekindDomain,
    parameter, rfl, parameter_irreducible, squareChainConclusion⟩

end UnconditionalCounterexample.PaperConstruction
