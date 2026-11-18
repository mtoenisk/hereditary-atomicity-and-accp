import UnconditionalCounterexample.PaperConclusion
import UnconditionalCounterexample.PaperCurveRecognition
import UnconditionalCounterexample.PaperSharpExtraction
import UnconditionalCounterexample.PaperStalkOrders

/-!
# A hereditarily atomic domain without ACCP

Theorems A and B and the results of §§3–5 for the subring of ℚ(t) defined by
`PaperConstruction.domain`. In the simultaneous realization a zero-based Lean
stage `n` has manuscript index `n + 1`.
-/

noncomputable section
namespace UnconditionalCounterexample.Manuscript

open Polynomial Filter PaperConstruction
open scoped BigOperators nonZeroDivisors

-- Manuscript: thm:main
/-- Theorem A for the concrete domain. The successive ratios in the strict
chain starting at the square of the coordinate are independent modulo ℚˣ. -/
theorem counterexample_domain :
    Factorization.IsHereditarilyAtomic domain ∧ IsFractionRing domain (RatFunc ℚ) ∧
    (∀ x : domain, IsUnit x ↔ x = 1 ∨ x = -1) ∧
    (∃ t : domain, (t : RatFunc ℚ) = RatFunc.X ∧ Irreducible t ∧
      PaperTargets.SquareChainConclusion domain t) ∧
    ¬ WfDvdMonoid domain ∧
    (∀ (M : Ideal domain) [M.IsMaximal], IsDiscreteValuationRing (Localization.AtPrime M)) ∧
    (∀ I : Ideal domain, I ≠ ⊥ → I ≠ ⊤ →
       ∃ L : List (Ideal domain), (∀ J ∈ L, J.IsRadical) ∧ L.prod = I) ∧
    Nonempty (Additive (CommRing.Pic domain) ≃+ (ℕ →₀ ZMod 3)) :=
  PaperConstruction.theoremAConclusion

-- Manuscript: thm:subrings
/-- Theorem B for all unital subrings of the domain in Theorem A. -/
theorem subring_classification (T : Subring domain) :
    (¬ WfDvdMonoid T ↔ ¬ Factorization.IsBFDomain T) ∧
    (¬ Factorization.IsBFDomain T ↔ Finite (domain ⧸ T.toAddSubgroup)) ∧
    (Finite (domain ⧸ T.toAddSubgroup) ↔
      ∃ n : ℕ, 0 < n ∧ T = PaperTargets.integerOrder domain n) ∧
    (∀ n : ℕ, 0 < n → T = PaperTargets.integerOrder domain n →
      T.toAddSubgroup.index = n ∧ RadicalConductor.conductorIdeal T = Ideal.span {(n : domain)}) ∧
    (Infinite (domain ⧸ T.toAddSubgroup) → Factorization.IsHereditarilyBF T) :=
  PaperConstruction.theoremBConclusion T

/-- The existential formulation with one common witness for both main theorems. -/
theorem exists_counterexample_with_classified_subrings :
    ∃ D : Subring (RatFunc ℚ), PaperTargets.TheoremAConclusion D ∧ PaperTargets.TheoremBConclusion D :=
  ⟨domain, counterexample_domain, subring_classification⟩

-- Manuscript: prop:construction
/-- The raw monic irreducibles and the predecessor powers defining the
normalized generators. Stage zero has empty predecessor product. -/
theorem stage_polynomials :
    StrictMono (fun n => (raw n).natDegree) ∧
    (∀ n, (raw n).Monic ∧ Irreducible (raw n) ∧ (raw n).coeff 0 ≠ 0 ∧ 0 < exponent n) ∧
    (∀ n, CompleteProfiles.generators raw exponent n =
      algebraMap ℚ[X] (RatFunc ℚ) (raw n) /
        ∏ j ∈ Finset.range n, (algebraMap ℚ[X] (RatFunc ℚ) (raw j)) ^ exponent n) ∧
    CompleteProfiles.generators raw exponent 0 = algebraMap ℚ[X] (RatFunc ℚ) (raw 0) := by
  refine ⟨construction.chain.raw_degree_strict, fun n => ⟨construction.chain.raw_monic n,
    construction.chain.raw_irreducible n, construction.chain.raw_constant_ne_zero n,
    construction.chain.exponent_pos n⟩, fun _ => rfl, ?_⟩
  change _ / (∏ j ∈ Finset.range 0, (algebraMap ℚ[X] (RatFunc ℚ) (raw j)) ^ exponent 0) = _
  simp

theorem chosen_branches (j : ℕ) :
    (∀ b, Transcendental ℚ (SequenceLocalTransfer.branch construction j b) ∧
      SequenceLocalTransfer.branch construction j b ∈ PadicInt.subring (PrimaryChoices.primes j).val) ∧
    (SequenceLocalTransfer.branch construction j false).valuation = (if j = 0 then 2 else 1) ∧
    IsUnit (places.guard (PrimaryChoices.primes j)) ∧
    SequenceLocalTransfer.branch construction j false ≠ SequenceLocalTransfer.branch construction j true :=
  ⟨fun b => ⟨SequenceLocalTransfer.branch_transcendental construction j b,
    SequenceLocalTransfer.branch_integral construction j b⟩, PrimaryChoices.primary_valuation j,
    construction.chain.guardChain.value_unit _, SequenceLocalTransfer.branch_ne construction j⟩

/-- The prescribed primary columns for the b and q generators and their unit
values at every guard, all for the same sequence of rational functions. -/
theorem generator_valuations :
    (∀ n j, PairedDomain.vertical places (.inl j)
      (CompleteProfiles.generators raw exponent (NormalizedWords.Generator.b n).stage) =
      WithZero.exp (-PrimaryWordProfiles.bWeight n j)) ∧
    (∀ n j, PairedDomain.vertical places (.inl j)
      (CompleteProfiles.generators raw exponent (NormalizedWords.Generator.q n).stage) =
      WithZero.exp (-PrimaryWordProfiles.qWeight n j)) ∧
    (∀ n p, PairedDomain.vertical places (.inr p) (CompleteProfiles.generators raw exponent n) = 1) :=
  ⟨generator_b_valuation, generator_q_valuation, generator_guard_valuation⟩

theorem eventual_orders (f : RatFunc ℚ) (hf : f ≠ 0) :
    (∀ᶠ j in atTop, DiscreteOrders.order (CompleteProfiles.valuations poles places (.primary j)) f =
      PrimaryStabilization.tOrder f) ∧
    {p : GuardSupport.PrimeIndex | PairedDomain.vertical places (.inr p) f ≠ 1}.Finite := by
  obtain ⟨N, hN⟩ := CompleteProfiles.eventually_primary poles places f hf
  exact ⟨eventually_atTop.mpr ⟨N, fun j hj => (hN j hj).trans
    (CompleteProfiles.limit_order poles places f hf)⟩, guardSupport f hf⟩

theorem atom_recurrence_and_returns :
    (atom 0 : RatFunc ℚ) = RatFunc.X ∧
    (∀ n, (atom (n + 1) : RatFunc ℚ) = (atom n : RatFunc ℚ) *
      construction.chain.b (n + 1) / construction.chain.q n) ∧
    ∀ m : ℕ, 0 < m → ∀ᶠ n in atTop, (m : domain) ∣ atom n - 1 :=
  ⟨coe_atom_zero, fun n => construction.chain.a_succ n, ConstructionReturns.eventually_integer_dvd_atom_sub_one⟩

open ConstructionWords

/-- The denominator is the monic product computed from the earlier raw
polynomials and the stage plan. Every root of an earlier factor is a pole. -/
theorem scheduled_word (n : ℕ) (w : Word n) :
    PaperWords.word n w = algebraMap ℚ[X] (RatFunc ℚ) (raw n) ^ w.latestExponent /
      algebraMap ℚ[X] (RatFunc ℚ) (PaperWords.denominator n w) ∧
    PaperWords.denominator n w = ∏ j : Fin n, raw j ^ (PaperWords.plan n).powers w j ∧
    (PaperWords.denominator n w).Monic ∧
    (PaperWords.word n w).denom.natDegree < (PaperWords.word n w).num.natDegree ∧
    ∀ j < n, ∀ a : AlgebraicClosure ℚ, (raw j).eval₂ (algebraMap ℚ _) a = 0 →
      (PaperWords.word n w).denom.eval₂ (algebraMap ℚ _) a = 0 :=
  ⟨PaperWords.word_eq_fraction n w, rfl, PaperWords.denominator_monic n w,
    PaperWords.pole_at_infinity n w, PaperWords.pole_at_earlier_root n w⟩

theorem scheduled_geometric_tests :
    (∀ a b : AlgebraicClosure ℚ, a ≠ b → PaperWords.Retained a → PaperWords.Retained b →
      ∀ᶠ n in atTop, ∀ w : Word n,
        RatFunc.eval (algebraMap ℚ _) a (PaperWords.word n w) ≠
          RatFunc.eval (algebraMap ℚ _) b (PaperWords.word n w)) ∧
    (∀ a : AlgebraicClosure ℚ, PaperWords.Retained a → ∀ᶠ n in atTop, ∀ w : Word n,
      CurveRecovery.geometricDerivativeAt (AlgebraicClosure ℚ) (PaperWords.word n w) a ≠ 0) ∧
    ∀ (j : ℕ) (b : Bool), ∀ᶠ n in atTop, ∀ w : Word n,
      (CurveRecovery.geometricDerivativeAt ℚ_[(PrimaryChoices.primes j).val] (PaperWords.word n w)
        (SequenceLocalTransfer.branch construction j b)).valuation < -((n + 1 : ℕ) : ℤ) :=
  ⟨PaperWords.eventually_separates, PaperWords.eventually_nonzero_derivative,
    PaperWords.eventually_derivative_bound⟩

open PrimaryChoices LocalAlgebra

theorem scaled_pair_integral (j s : ℕ) :
    RatFunc.C ((primes j).val : ℚ_[(primes j).val]) ^ (2 * s) *
      ((RatFunc.X - RatFunc.C (SequenceLocalTransfer.branch construction j false)) *
       (RatFunc.X - RatFunc.C (SequenceLocalTransfer.branch construction j true))) ∈
      padicScaledPolynomialRing (primes j).val s :=
  scaled_pair_mem_scaledPolynomialRing _ _ _ _ _ (by simp)
    (SequenceLocalTransfer.branch_integral construction j false)
    (SequenceLocalTransfer.branch_integral construction j true) _ _

/-- With g = p^(2s)(t−α)(t−β), the same listed fraction satisfies
g^a = p^(n+1)(u+vw) with both coefficients in ℤ_p[p^s t]. -/
theorem scheduled_local_transfer (j s : ℕ) :
    ∀ᶠ n in atTop, ∀ w : Word n, ∃ U V : padicScaledPolynomialRing (primes j).val s,
      (RatFunc.C ((primes j).val : ℚ_[(primes j).val]) ^ (2 * s) *
        ((RatFunc.X - RatFunc.C (SequenceLocalTransfer.branch construction j false)) *
         (RatFunc.X - RatFunc.C (SequenceLocalTransfer.branch construction j true)))) ^ w.latestExponent =
        RatFunc.C ((primes j).val : ℚ_[(primes j).val]) ^ (n + 1) *
        ((U : RatFunc ℚ_[(primes j).val]) + (V : RatFunc ℚ_[(primes j).val]) *
          (((raw n).map (algebraMap ℚ ℚ_[(primes j).val]) : RatFunc ℚ_[(primes j).val]) ^
             w.latestExponent /
           ((PaperWords.denominator n w).map (algebraMap ℚ ℚ_[(primes j).val]) :
             RatFunc ℚ_[(primes j).val]))) := by
  filter_upwards [SequenceLocalTransfer.eventually_all_word_estimates construction j s] with n hn
  exact fun w => (hn w).2

-- Manuscript: lem:stalks
theorem fraction_field_and_localization :
    IsFractionRing domain (RatFunc ℚ) ∧
    (∀ q : ℚ, (q : RatFunc ℚ) ∈ domain ↔ ∃ z : ℤ, (z : ℚ) = q) ∧
    IsLocalization (IntersectionDomain.integerDenominators domain) (PoleAlgebra.generated poles) :=
  ⟨fractionRing, rational_mem_iff_integer, integerLocalization⟩

open PaperMaximalSpectrum

theorem maximal_centers_and_stalks :
    (∀ M : Ideal domain, M.IsMaximal ↔ ∃! p : Point, center p = M) ∧
    (∀ i : Vertical, Nonempty (Localization.AtPrime (center (.inl i)) ≃ₐ[domain]
      (valuation (.inl i)).valuationSubring)) ∧
    (∀ h : Horizontal, Nonempty (Localization.AtPrime (center (.inr h)) ≃+*
      (HorizontalOrders.valuation h.val).valuationSubring)) ∧
    ∀ (M : Ideal domain) [M.IsMaximal], IsDiscreteValuationRing (Localization.AtPrime M) := by
  refine ⟨?_, fun i => ⟨verticalStalkEquiv i⟩, fun h => by
    let := horizontalDomainAlgebra h
    exact ⟨(horizontalStalkEquiv h).toRingEquiv⟩,
    isAlmostDedekindDomain⟩
  intro M
  constructor
  · intro hM
    obtain ⟨p, hp⟩ := exists_center_of_maximal M
    exact ⟨p, hp, fun q hq => center_injective (hq.trans hp.symm)⟩
  · rintro ⟨p, rfl, _⟩
    exact center_isMaximal p

-- Manuscript: prop:ideals
/-- The actual invertible ideal profiles are precisely the restricted
integer-valued functions on the full set of places. -/
theorem invertible_ideal_profiles (f : PaperIdealProfiles.Label → ℤ) :
    (∃ I : Additive PaperIdealProfiles.Fractionalˣ, PaperIdealProfiles.profileFunction I = f) ↔
    (∃ N : ℕ, ∀ j, N ≤ j → f (.primary j) = f .limit) ∧
      {o | f (.outside o) ≠ 0}.Finite := by
  constructor
  · rintro ⟨I, rfl⟩
    exact PaperIdealProfiles.profileFunction_restricted I
  · intro hf
    obtain ⟨p, hp⟩ := PicardProfiles.exists_coordinate f hf
    obtain ⟨I, hI⟩ := PaperIdealProfiles.profileMap_surjective p
    exact ⟨I, (PaperIdealProfiles.coordinate_profileMap I).symm.trans
      ((congrArg PicardProfiles.coordinate hI).trans hp)⟩

theorem radical_factorization_units_and_picard :
    (∀ I : Ideal domain, I ≠ ⊥ → I ≠ ⊤ →
      ∃ L : List (Ideal domain), (∀ J ∈ L, J.IsRadical) ∧ L.prod = I) ∧
    (∀ x : domain, IsUnit x ↔ x = 1 ∨ x = -1) ∧
    Nonempty (Additive (CommRing.Pic domain) ≃+ (ℕ →₀ ZMod 3)) :=
  ⟨isSPDomain, isUnit_iff_sign, ⟨PaperPicard.picardEquiv⟩⟩

-- Manuscript: cor:chain
theorem square_chain_with_independent_ratios :
    ∃ q x : ℕ → domain,
      (∀ n, q n ≠ 0 ∧ ¬ IsUnit (q n)) ∧ (∀ n, x n ≠ 0) ∧ x 0 = parameter ^ 2 ∧
      (∀ n, (x n : RatFunc ℚ) = (parameter : RatFunc ℚ) ^ 2 /
        ∏ j ∈ Finset.range n, (q (2 * j) : RatFunc ℚ)) ∧
      (∀ n, x n = q (2 * n) * x (n + 1)) ∧
      StrictMono (fun n => Ideal.span ({x n} : Set domain)) ∧
      (∀ j, q (2 * j) ≠ 0) ∧
      ∀ (e : ℕ →₀ ℤ) (c : ℚ), c ≠ 0 →
        e.prod (fun j m => ((q (2 * j) : domain) : RatFunc ℚ) ^ m) = RatFunc.C c → e = 0 :=
  squareChainConclusion

-- Manuscript: lem:extraction
theorem escaping_divisor (T : Subring domain) (x : T) (hx : x ≠ 0)
    (hunbounded : ¬ Factorization.HasBoundedFactorizations x) (N M : ℕ) :
    let r := sSup (Set.range (fun j => valuationProfiles.value (.primary j) (x : domain)))
    ∃ y : T, IsEscapingPrimaryDivisor valuationProfiles T x y r N ∧
      ∃ e : ℕ →₀ ℤ,
        (((y : domain) : RatFunc ℚ) = PrincipalProfiles.word (CompleteProfiles.generators raw exponent) e ∨
         ((y : domain) : RatFunc ℚ) = -PrincipalProfiles.word (CompleteProfiles.generators raw exponent) e) ∧
        (∀ j, |e j| ≤ (2 * r : ℕ)) ∧ ∃ n : ℕ, M < n ∧ 0 < e n ∧ ∀ j, n < j → e j = 0 :=
  PaperSharpExtraction.exists_divisor_word_beyond T x hx hunbounded N M

/-- One sequence of the sharp divisors has escaping primary support and
last stages tending to infinity. Its exponent budget is independent of n. -/
theorem escaping_divisor_sequence (T : Subring domain) (x : T) (hx : x ≠ 0)
    (hunbounded : ¬ Factorization.HasBoundedFactorizations x) :
    let r := sSup (Set.range (fun j => valuationProfiles.value (.primary j) (x : domain)))
    ∃ (y : ℕ → T) (e : ℕ → ℕ →₀ ℤ) (stage : ℕ → ℕ), Tendsto stage atTop atTop ∧
      ∀ n, IsEscapingPrimaryDivisor valuationProfiles T x (y n) r n ∧
        ((((y n : T) : domain) : RatFunc ℚ) = PrincipalProfiles.word (CompleteProfiles.generators raw exponent) (e n) ∨
         (((y n : T) : domain) : RatFunc ℚ) = -PrincipalProfiles.word (CompleteProfiles.generators raw exponent) (e n)) ∧
        (∀ j, |e n j| ≤ (2 * r : ℕ)) ∧ 0 < e n (stage n) ∧ ∀ j, stage n < j → e n j = 0 := by
  dsimp only
  choose y hy e hsign hbound stage hlate hpos htop using
    fun n => escaping_divisor T x hx hunbounded n n
  exact ⟨y, e, stage, tendsto_atTop_mono (fun n => (hlate n).le) tendsto_id,
    fun n => ⟨hy n, hsign n, hbound n, hpos n, htop n⟩⟩

-- Manuscript: lem:curve-recognition
theorem recognize_pole_algebra
    (A : Subalgebra ℚ PaperCurveRecognition.B)
    (hpoles : ∀ a : AlgebraicClosure ℚ, ¬ PaperWords.Retained a → ∃ f : A,
      ((f : PaperCurveRecognition.B) : RatFunc ℚ).denom.eval₂ (algebraMap ℚ _) a = 0)
    (hinfinity : ∃ f : A, ((f : PaperCurveRecognition.B) : RatFunc ℚ).denom.natDegree <
      ((f : PaperCurveRecognition.B) : RatFunc ℚ).num.natDegree)
    (hsep : ∀ a b : AlgebraicClosure ℚ, PaperWords.Retained a → PaperWords.Retained b → a ≠ b →
      ∃ f : A, RatFunc.eval (algebraMap ℚ _) a ((f : PaperCurveRecognition.B) : RatFunc ℚ) ≠
        RatFunc.eval (algebraMap ℚ _) b ((f : PaperCurveRecognition.B) : RatFunc ℚ))
    (htangent : ∀ a : AlgebraicClosure ℚ, PaperWords.Retained a → ∃ f : A,
      CurveRecovery.geometricDerivativeAt (AlgebraicClosure ℚ) ((f : PaperCurveRecognition.B) : RatFunc ℚ) a ≠ 0) :
    A = ⊤ :=
  PaperCurveRecognition.subalgebra_eq_top A hpoles hinfinity hsep htangent

-- Manuscript: prop:generic
theorem generic_fiber_and_coordinate (T : Subring domain) (x : T) (hx : x ≠ 0)
    (hunbounded : ¬ Factorization.HasBoundedFactorizations x) :
    RationalHull.hull (T.map PaperInclusion.inclusion) = ⊤ ∧
    ∃ n : ℕ, 0 < n ∧ (n : domain) * PaperInclusion.coordinate ∈ T :=
  ⟨PaperGenericRecovery.hull_eq_top_of_unbounded T x hx hunbounded,
    PaperGenericRecovery.exists_nat_coordinate_mem_of_unbounded T x hx hunbounded⟩

end UnconditionalCounterexample.Manuscript
