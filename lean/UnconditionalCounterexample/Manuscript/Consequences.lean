import UnconditionalCounterexample.PaperSharpExtraction
import UnconditionalCounterexample.PaperConductor
import UnconditionalCounterexample.PaperIntegerOrders
import UnconditionalCounterexample.ExponentTwoPrufer
import UnconditionalCounterexample.PaperVariation

/-!
# Conductors, finite-index orders, and sharpness

Statements from §§6–8 of *A hereditarily atomic domain without ACCP*.
Throughout §§6–7 the domain and the parameter are those of Theorem A.
-/

noncomputable section

namespace UnconditionalCounterexample.Manuscript

open PaperConstruction Polynomial

/-- The image of the polynomial with roots the two selected branches in the
scalar-extended pole algebra at the indexed rational prime. -/
abbrev branchPolynomial (j : ℕ) :
    PoleAlgebra.generated (ScalarExtension.extendedSet ℚ ℚ_[(PrimaryChoices.primes j).val] poles) :=
  algebraMap ℚ_[(PrimaryChoices.primes j).val][X] _
    ((X - C (SequenceLocalTransfer.branch construction j false)) *
      (X - C (SequenceLocalTransfer.branch construction j true)))

-- Manuscript: lem:exact-transfer
/-- Lemma 6.1. The exponent is twice the supremum of the primary orders of the given element. -/
theorem exactPolynomialTransfer (T : Subring domain) (x : T) (hx : x ≠ 0)
    (hu : ¬ Factorization.HasBoundedFactorizations x) (j : ℕ) :
    ∀ z ∈ Ideal.span {branchPolynomial j ^
        (2 * sSup (Set.range fun i => valuationProfiles.value (.primary i) (x : domain)))},
      z ∈ PaperLocalConductor.localImage j T := by
  obtain ⟨n, hn, hnt⟩ := PaperGenericRecovery.exists_nat_coordinate_mem_of_unbounded T x hx hu
  simpa only [branchPolynomial, ← map_pow, PaperSharpExtraction.primaryBound_eq,
    PaperLocalConductor.localImage] using
    PaperSharpExtraction.sharp_power_ideal_subset_at_prescribed_scale T x hx hu n hn hnt j

-- Manuscript: lem:local-conductor
/-- Lemma 6.2. The conductor of the ordinary integral tensor image is the ideal
of the two branches, to the first power. -/
theorem pairedLocalConductor (T : Subring domain) (x : T) (hx : x ≠ 0)
    (hu : ¬ Factorization.HasBoundedFactorizations x) (j : ℕ) :
    RadicalConductor.conductorIdeal (PaperLocalConductor.localImage j T) =
      Ideal.span {branchPolynomial j} :=
  PaperConductor.conductor_eq_pair_of_unbounded T x hx hu j

-- Manuscript: thm:conductor
/-- Theorem 6.3. Every positive integer which clears the parameter into the
original subring carries the whole domain into that same subring. -/
theorem integerConductor (T : Subring domain) (x : T) (hx : x ≠ 0)
    (hu : ¬ Factorization.HasBoundedFactorizations x) :
    (∃ n : ℕ, 0 < n ∧ (n : domain) * parameter ∈ T) ∧
      ∀ n : ℕ, 0 < n → (n : domain) * parameter ∈ T →
        ∀ z : domain, (n : domain) * z ∈ T :=
  PaperIntegerConductor.integer_conductor T x hx hu

-- Manuscript: lem:low-order
/-- Lemma 7.1. Low order gives finitely many divisor classes, and all the
elements of the constructed atom sequence are irreducible. -/
theorem lowOrderDivisorsAndAtoms :
    (∀ x : domain, x ≠ 0 → PrimaryStabilization.tOrder (x : RatFunc ℚ) ≤ 1 →
      {a : Associates domain | a ∣ Associates.mk x}.Finite) ∧
      ∀ n : ℕ, Irreducible (atom n) :=
  ⟨finite_associates_divisors_of_order_le_one, atom_irreducible⟩

-- Manuscript: prop:all-atomic
/-- Proposition 7.2. Each unital subring is atomic. In an order containing
a positive integer multiple of the domain, count factors using their actual
orders of vanishing at zero. -/
theorem atomicSubringsAndFactorCount (T : Subring domain) :
    Factorization.IsAtomicDomain T ∧
      ∀ m : ℕ, 0 < m → (∀ z : domain, (m : domain) * z ∈ T) →
      ∀ x : T, x ≠ 0 → ¬ IsUnit x → ∀ L : Multiset T,
      (∀ z ∈ L, Irreducible z) → Associated L.prod x →
        ((L.filter (fun z : T => PrimaryStabilization.tOrder ((z : domain) : RatFunc ℚ) = 1)).card : ℤ) =
          PrimaryStabilization.tOrder ((x : domain) : RatFunc ℚ) ∧
        ∀ z ∈ L, PrimaryStabilization.tOrder ((z : domain) : RatFunc ℚ) ≠ 1 →
          PrimaryStabilization.tOrder ((z : domain) : RatFunc ℚ) = 0 := by
  refine ⟨hereditarilyAtomic T, ?_⟩
  intro m hm hcon x hx _ L hAtoms hProd
  obtain ⟨hcount, hothers⟩ := factor_count T m hm hcon hx L hAtoms hProd
  have hval (z : T) (hz : z ∈ L) := valuationProfiles_limit_cast (z : domain)
    (fun he => (hAtoms z hz).ne_zero (Subtype.ext he))
  have hfilter : L.filter (fun z : T => PrimaryStabilization.tOrder ((z : domain) : RatFunc ℚ) = 1) =
      L.filter (fun z : T => valuationProfiles.value .limit (z : domain) = 1) := by
    apply Multiset.filter_congr
    intro z hz
    rw [← hval z hz]
    norm_cast
  refine ⟨?_, ?_⟩
  · rw [hfilter, hcount, valuationProfiles_limit_cast _ (fun h => hx (Subtype.ext h))]
  · intro z hz hn
    rw [← hval z hz] at hn ⊢
    exact_mod_cast hothers z hz (fun h => hn (by exact_mod_cast h))

-- Manuscript: prop:finite-index
/-- Proposition 7.3. The unique subring of each positive index, its paired
residue test, the actual additive generator, and its conductor. -/
theorem integerOrderClassification (n : ℕ) (hn : 0 < n) :
    let T := PaperTargets.integerOrder domain n
    T.toAddSubgroup.index = n ∧
      (∀ S : Subring domain, S.toAddSubgroup.index = n → S = T) ∧
      (∀ x : domain, x ∈ T ↔ ∀ p : n.primeFactors,
        let values := PairedResidues.primePairResidue poles places
          ⟨p, Nat.prime_of_mem_primeFactors p.property⟩ (n.factorization p) x
        values.1 = values.2) ∧
      (∀ x : domain ⧸ T.toAddSubgroup, ∃ z : ℤ,
        z • QuotientAddGroup.mk' T.toAddSubgroup parameter = x) ∧
      RadicalConductor.conductorIdeal T = Ideal.span {(n : domain)} := by
  refine ⟨integer_order_index n hn, ?_, ?_, integer_order_quotient_generated_by_parameter n hn,
    integer_order_conductor n hn⟩
  · exact fun S hS => FiniteOrders.eq_integerOrder_of_index_eq S n hn (integer_order_index n hn) hS
  · exact PairedResidues.mem_order_iff_prime_congruences poles places n hn.ne'

-- Manuscript: prop:chain-height
/-- Proposition 7.4. Classify starting ideals and lengths of atom factorizations
in a finite-index subring by the order of the given element at zero. -/
theorem chainHeightAndFactorizations (T : Subring domain) (hfinite : Finite (domain ⧸ T.toAddSubgroup))
    (x : T) (hx : x ≠ 0) :
    let v := PrimaryStabilization.tOrder ((x : domain) : RatFunc ℚ)
    ((∃ a : ℕ → T, a 0 = x ∧ (∀ i, a i ≠ 0) ∧ StrictMono (fun i => Ideal.span {a i})) ↔ 2 ≤ v) ∧
      (2 ≤ v → ¬ BddAbove (Factorization.factorizationLengths x)) ∧
      (v ≤ 1 → (Multiset.map Associates.mk ''
        {L : Multiset T | (∀ a ∈ L, Irreducible a) ∧ Associated L.prod x}).Finite) := by
  exact ⟨finite_index_chain_height T hfinite x hx, finite_index_atom_lengths_unbounded T hfinite x hx,
    fun hv => (finite_subring_factorizations_of_order_le_one T x hx hv).image _⟩

-- Manuscript: prop:exponent-two
/-- Proposition 8.1. An atom generates a radical ideal or the square of an
invertible maximal ideal. An atomic domain satisfying the hypotheses is
Dedekind in the convention including fields. -/
theorem exponentTwoPrufer {R : Type*} [CommRing R] [IsDomain R]
    (hPrufer : ExponentTwo.IsPruferDomain R) (hPic : ∀ c : CommRing.Pic R, c ^ 2 = 1) :
    (∀ a : R, Irreducible a → (Ideal.span {a}).IsRadical ∨ ∃ M : Ideal R,
      M.IsMaximal ∧ IsUnit (M : ExponentTwo.FracIdeal R) ∧ Ideal.span {a} = M ^ 2) ∧
      (Factorization.IsAtomicDomain R → IsDedekindDomain R) :=
  ⟨fun _ ha => ExponentTwo.atom_radical_or_square_maximal hPrufer hPic ha,
    ExponentTwo.dedekind_of_atomic_prufer_picard_two hPrufer hPic⟩

-- Manuscript: cor:variation
/-- Corollary 8.2. The isomorphism distinction is between abstract rings, and
the cardinality, Picard groups, and chains use the same family. -/
theorem continuumOfNonisomorphicDomains :
    ∃ rings : Set (Subring (RatFunc ℚ)), Cardinal.mk rings = Cardinal.continuum ∧
      (∀ D ∈ rings, Factorization.IsHereditarilyAtomic D ∧ IsAlmostDedekindDomain D ∧
        PaperTargets.IsSPDomain D ∧ IsFractionRing D (RatFunc ℚ) ∧
        Nonempty (Additive (CommRing.Pic D) ≃+ (ℕ →₀ ZMod 3)) ∧
        ∃ a : D, Irreducible a ∧ ∃ I : ℕ → Ideal D,
          I 0 = Ideal.span {a ^ 2} ∧ StrictMono I ∧ ∀ i, (I i).IsPrincipal) ∧
        ∀ D ∈ rings, ∀ E ∈ rings, D ≠ E → ¬ Nonempty (D ≃+* E) :=
  MixedVariation.continuum_many

end UnconditionalCounterexample.Manuscript
