import UnconditionalCounterexample.MixedAtoms
import UnconditionalCounterexample.ConstructionReturns
import UnconditionalCounterexample.MixedSequenceArguments
import UnconditionalCounterexample.MixedReturnPrefix
import UnconditionalCounterexample.SparseReturnCongruences

noncomputable section
namespace UnconditionalCounterexample.MixedConstructionReturns
open Polynomial Filter PrimaryTargets RecursivePrefix ConstructionWords MixedConstruction

variable (S : Set GuardSupport.PrimeIndex) (hS : S.Infinite)

def evaluationPrime (p : GuardSupport.PrimeIndex) (b : Bool)
    (hb : MixedStageSelection.Active ((primaryData S hS).paired p) b) :
    RatFunc ℚ →+* ℚ_[p.val] :=
  match b with
  | true => GuardSupport.guardEvaluation (places S hS).guard (places S hS).guard_trans p
  | false => EvaluationDVR.evaluationHom _
      ((primaryData S hS).value p (hb.resolve_left (by decide))).val
      ((primaryData S hS).transcendental p (hb.resolve_left (by decide)))

def evaluationBranch (j : ℕ) (b : Bool)
    (hb : MixedStageSelection.Active ((primaryData S hS).paired (PrimaryChoices.primes j)) b) :
    RatFunc ℚ →+* ℚ_[(PrimaryChoices.primes j).val] :=
  EvaluationDVR.evaluationHom _ (MixedSequenceArguments.branch (construction S hS) j b)
    (MixedSequenceArguments.branch_transcendental (construction S hS) j b hb)

theorem evaluationBranch_eq_prime (j : ℕ) (b : Bool)
    (hb : MixedStageSelection.Active ((primaryData S hS).paired (PrimaryChoices.primes j)) b) :
    evaluationBranch S hS j b hb = evaluationPrime S hS (PrimaryChoices.primes j) b hb := by
  cases b with
  | true => rfl
  | false =>
    have he := MixedSequenceArguments.branch_false (construction S hS) j (hb.resolve_left (by decide))
    unfold evaluationBranch evaluationPrime
    congr 1

/-- The actual mixed q Choice gives the refined return at every active entry. -/
theorem q_return_selected (n : ℕ) :
    let s := (construction S hS).selection (2 * n + 2)
    ∀ i : s.batch.indices, ∀ b : Bool,
      ∀ hb : MixedStageSelection.Active ((primaryData S hS).paired (PrimaryChoices.primes i.val)) b,
      ReturnTargets.IsRefined (branchOrder S hS (2 * n + 2) (PrimaryChoices.primes i.val) b)
        (EvaluationDVR.evaluationHom (s.batch.primeAt i) ((primaryData S hS).branch s.batch i b)
          ((primaryData S hS).branch_transcendental s.batch i b hb)
          ((construction S hS).chain.a n * (construction S hS).chain.b (n + 1))) →
      (EvaluationDVR.evaluationHom (s.batch.primeAt i) ((primaryData S hS).branch s.batch i b)
          ((primaryData S hS).branch_transcendental s.batch i b hb)
          ((construction S hS).chain.a (n + 1)) - 1) /
        (s.batch.primeAt i : ℚ_[s.batch.primeAt i]) ^ n ∈ PadicInt.subring (s.batch.primeAt i) := by
  dsimp only
  let s := (construction S hS).selection (2 * n + 2)
  let P := (construction S hS).chain.approx (2 * n + 2)
  have hlocal := MixedReturnPrefix.choice_q_actual s.batch.primeAt
    (fun i => (primaryData S hS).paired (PrimaryChoices.primes i.val))
    s.batch.auxiliary.val n P s.plan ((primaryData S hS).branch s.batch)
    ((targets S hS P s.batch).value) ((primaryData S hS).branch_transcendental s.batch)
    (fun i b => branchOrder S hS (2 * n + 2) (PrimaryChoices.primes i.val) b)
    ((targets S hS P s.batch).precision) s.choice
    (by
      intro i b hb
      simp only [targets, dite_eq_left hb, generatorAt_even_succ, Prefix.generatorTarget])
    (by
      intro i b hb
      simp only [targets, dite_eq_left hb, generatorAt_even_succ, Prefix.generatorPrecision])
    s.toNext rfl rfl
  intro i b hb href
  have h := hlocal i b hb
  dsimp only [P] at h
  rw [(construction S hS).chain.a_agrees_before_q n,
    (construction S hS).chain.b_succ_agrees_before_q n] at h
  have hnext : (construction S hS).chain.next (2 * n + 2) = s.toNext :=
    (construction S hS).consistent _
  rw [← hnext, ← (construction S hS).chain.a_succ_eq_appended n] at h
  exact h href

theorem q_return_processed (n j : ℕ) (b : Bool)
    (hb : MixedStageSelection.Active ((primaryData S hS).paired (PrimaryChoices.primes j)) b)
    (hj : PrimaryChoices.primes j ∈ ((construction S hS).selection (2 * n + 2)).batch.processed.primes)
    (href : ReturnTargets.IsRefined (branchOrder S hS (2 * n + 2) (PrimaryChoices.primes j) b)
      (evaluationBranch S hS j b hb
        ((construction S hS).chain.a n * (construction S hS).chain.b (n + 1)))) :
    (evaluationBranch S hS j b hb ((construction S hS).chain.a (n + 1)) - 1) /
      ((PrimaryChoices.primes j).val : ℚ_[(PrimaryChoices.primes j).val]) ^ n ∈
        PadicInt.subring (PrimaryChoices.primes j).val := by
  let s := (construction S hS).selection (2 * n + 2)
  let i : s.batch.indices := ⟨j, (s.batch.mem_indices j).mpr hj⟩
  have h := q_return_selected S hS n i b hb
  have he := MixedSequenceArguments.selection_branch_eq (construction S hS) (2 * n + 2) i b
  change (primaryData S hS).branch s.batch i b =
    MixedSequenceArguments.branch (construction S hS) j b at he
  have heval : EvaluationDVR.evaluationHom (s.batch.primeAt i)
      ((primaryData S hS).branch s.batch i b)
      ((primaryData S hS).branch_transcendental s.batch i b hb) =
        evaluationBranch S hS j b hb := by
    unfold evaluationBranch
    congr 1
  change (ReturnTargets.IsRefined _ ((EvaluationDVR.evaluationHom (s.batch.primeAt i)
    ((primaryData S hS).branch s.batch i b)
    ((primaryData S hS).branch_transcendental s.batch i b hb)) _) → _) at h
  rw [heval] at h
  exact h href

theorem q_return_prime (n : ℕ) (p : GuardSupport.PrimeIndex) (b : Bool)
    (hb : MixedStageSelection.Active ((primaryData S hS).paired p) b)
    (hp : p.val ≤ 2 * n + 2 + 1)
    (href : ReturnTargets.IsRefined (branchOrder S hS (2 * n + 2) p b)
      (evaluationPrime S hS p b hb
        ((construction S hS).chain.a n * (construction S hS).chain.b (n + 1)))) :
    (evaluationPrime S hS p b hb ((construction S hS).chain.a (n + 1)) - 1) /
      (p.val : ℚ_[p.val]) ^ n ∈ PadicInt.subring p.val := by
  obtain ⟨j, rfl⟩ := PrimaryChoices.primes.surjective p
  have h := q_return_processed S hS n j b hb
    (MixedSequenceArguments.processed_of_le (construction S hS) _ _ hp)
  rw [evaluationBranch_eq_prime] at h
  exact h href

theorem evaluationPrime_primary (i : ℕ)
    (hb : MixedStageSelection.Active ((primaryData S hS).paired ((places S hS).primes i)) false) :
    evaluationPrime S hS ((places S hS).primes i) false hb =
      SparsePrimaryDomain.evaluationAt (places S hS) (.inl i) := by
  have he : (primaryData S hS).value ((places S hS).primes i) (hb.resolve_left (by decide)) =
      (places S hS).primary i :=
    MixedGeneratorProfiles.primary_value_eq S hS i _
  have hev := congrArg Subtype.val he
  dsimp only [evaluationPrime, SparsePrimaryDomain.evaluationAt]
  exact MixedSequenceValuations.evaluationHom_congr _ _ _ hev

@[simp] theorem evaluationPrime_guard (p : GuardSupport.PrimeIndex)
    (hb : MixedStageSelection.Active ((primaryData S hS).paired p) true) :
    evaluationPrime S hS p true hb = SparsePrimaryDomain.evaluationAt (places S hS) (.inr p) := rfl

/-- The prior product is a unit at every fixed primary once the moving atom
support has passed that primary. -/
theorem prior_product_primary_norm_one (n i : ℕ) (hi : i < 2 * n) :
    ‖SparsePrimaryDomain.evaluationAt (places S hS) (.inl i)
      ((construction S hS).chain.a n * (construction S hS).chain.b (n + 1))‖ = 1 := by
  apply ConstructionReturns.norm_eq_one_of_mulValuation_eq_one
  have ha := SparseAtoms.a_primary (raw S hS) (exponent S hS) (places S hS)
    (MixedGeneratorProfiles.generatorProfiles S hS)
    (SparsePrimaryDomain.ofSelected_primary_zero S hS _ _) n i
  have hb := MixedGeneratorProfiles.generator_b_valuation S hS (n + 1) i
  rw [primaryAtomProfile_of_lt hi] at ha
  have hib : i ≠ 2 * (n + 1) := by omega
  simp only [PrimaryWordProfiles.bWeight, hib, ite_false, neg_zero, WithZero.exp_zero] at hb
  simp only [neg_zero, WithZero.exp_zero] at ha
  change SparsePrimaryDomain.vertical (places S hS) (.inl i)
    ((construction S hS).chain.a n * (construction S hS).chain.b (n + 1)) = 1
  rw [map_mul]
  change SparsePrimaryDomain.vertical (places S hS) (.inl i)
      (ReturnPrefix.a (SparseProfiles.generators (raw S hS) (exponent S hS)) n) *
    SparsePrimaryDomain.vertical (places S hS) (.inl i)
      (SparseProfiles.generators (raw S hS) (exponent S hS)
        (NormalizedWords.Generator.b (n + 1)).stage) = 1
  rw [ha, hb, one_mul]

/-- Every guard, paired or sole, sees the prior product as a unit. -/
theorem prior_product_guard_norm_one (n : ℕ) (p : GuardSupport.PrimeIndex) :
    ‖SparsePrimaryDomain.evaluationAt (places S hS) (.inr p)
      ((construction S hS).chain.a n * (construction S hS).chain.b (n + 1))‖ = 1 := by
  apply ConstructionReturns.norm_eq_one_of_mulValuation_eq_one
  have ha := SparseAtoms.a_guard (raw S hS) (exponent S hS) (places S hS)
    (MixedGeneratorProfiles.generatorProfiles S hS) (construction S hS).chain.guardChain.value_unit n p
  have hb := MixedGeneratorProfiles.generator_guard_valuation S hS
    (NormalizedWords.Generator.b (n + 1)).stage p
  change SparsePrimaryDomain.vertical (places S hS) (.inr p)
    ((construction S hS).chain.a n * (construction S hS).chain.b (n + 1)) = 1
  rw [map_mul]
  change SparsePrimaryDomain.vertical (places S hS) (.inr p)
      (ReturnPrefix.a (SparseProfiles.generators (raw S hS) (exponent S hS)) n) *
    SparsePrimaryDomain.vertical (places S hS) (.inr p)
      (SparseProfiles.generators (raw S hS) (exponent S hS)
        (NormalizedWords.Generator.b (n + 1)).stage) = 1
  rw [ha, hb, one_mul]

theorem q_branchOrder_selected_zero (n i : ℕ) (hi : i < 2 * n) :
    branchOrder S hS (2 * n + 2) ((places S hS).primes i) false = 0 := by
  change branchOrder S hS (2 * n + 2) (SelectedPrimes.primes S hS i) false = 0
  rw [branchOrder_selected, primaryOrder_even_succ]
  split_ifs <;> omega

/-- Every retained primary eventually receives the actual refined return. -/
theorem eventually_primary_returns (i : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      (SparsePrimaryDomain.evaluationAt (places S hS) (.inl i)
        ((construction S hS).chain.a (n + 1)) - 1) /
      ((SparsePrimaryDomain.primeAt (places S hS) (.inl i)).val :
        ℚ_[(SparsePrimaryDomain.primeAt (places S hS) (.inl i)).val]) ^ n ∈
        PadicInt.subring (SparsePrimaryDomain.primeAt (places S hS) (.inl i)).val := by
  filter_upwards [eventually_ge_atTop (max (i + 1) ((places S hS).primes i).val)] with n hn
  have hi : i < 2 * n := by omega
  have hb : MixedStageSelection.Active ((primaryData S hS).paired ((places S hS).primes i)) false :=
    Or.inr ⟨i, rfl⟩
  have h := q_return_prime S hS n ((places S hS).primes i) false hb (by omega)
  rw [evaluationPrime_primary] at h
  exact h ⟨q_branchOrder_selected_zero S hS n i hi, prior_product_primary_norm_one S hS n i hi⟩

/-- Every guard eventually receives the actual refined return, including the
sole guard above each omitted primary prime. -/
theorem eventually_guard_returns (p : GuardSupport.PrimeIndex) :
    ∀ᶠ n : ℕ in atTop,
      (SparsePrimaryDomain.evaluationAt (places S hS) (.inr p)
        ((construction S hS).chain.a (n + 1)) - 1) /
        ((SparsePrimaryDomain.primeAt (places S hS) (.inr p)).val :
          ℚ_[(SparsePrimaryDomain.primeAt (places S hS) (.inr p)).val]) ^ n ∈
          PadicInt.subring (SparsePrimaryDomain.primeAt (places S hS) (.inr p)).val := by
  filter_upwards [eventually_ge_atTop p.val] with n hn
  have hb : MixedStageSelection.Active ((primaryData S hS).paired p) true := Or.inl rfl
  have h := q_return_prime S hS n p true hb (by omega)
  rw [evaluationPrime_guard] at h
  exact h ⟨rfl, prior_product_guard_norm_one S hS n p⟩

/-- The literal actual atom sequence approaches one modulo every positive
integer inside this very same sparse intersection domain. -/
theorem eventually_integer_dvd_atom_sub_one (m : ℕ) (hm : 0 < m) :
    ∀ᶠ n : ℕ in atTop, (m : domain S hS) ∣ atom S hS n - 1 := by
  apply SparsePrimaryDomain.eventually_integer_dvd_of_refined_returns
    (places S hS) (poles S hS) (atom S hS) _ m hm
  rintro (i | p)
  · simpa only [coe_atom] using eventually_primary_returns S hS i
  · simpa only [coe_atom] using eventually_guard_returns S hS p

end UnconditionalCounterexample.MixedConstructionReturns
