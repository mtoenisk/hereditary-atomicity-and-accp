import UnconditionalCounterexample.GlobalPlans
import UnconditionalCounterexample.LocalAlgebra.ScaledPolynomial

/-!
# Local estimates for the actual recursively selected sequence

The finite-stage selection stores its coefficient estimates. These theorems
turn those estimates into actual scaled-polynomial transfer identities and
ordinary word-derivative valuation bounds for the polynomial that was appended.

Every fixed prime is ordinarily processed at all sufficiently late stages.
The finite batch arguments agree exactly with the permanent primary and guard
arguments of the same sequence. GlobalPlans transports the old denominator
products to the common infinite raw/exponent family. Thus every scheduled word
has both required local conclusions, simultaneously, with no new polynomial
choice and no additional transfer or derivative hypothesis. Raw stage n uses
positive arithmetic precision n+1.
-/

noncomputable section
namespace UnconditionalCounterexample.SequenceLocalTransfer

open Polynomial Filter ConstructionWords StageRecursion CombinedGuardStep
open PrimaryChoices GuardSupport LocalAlgebra

variable {R : Requirements} {n : ℕ} {P : RecursivePrefix.Prefix n}

theorem selection_raw_map (sel : Selection R P) (j : sel.batch.indices) :
    sel.raw.map (algebraMap ℚ ℚ_[sel.batch.primeAt j]) =
      ShiftedEisenstein.monicFamily (sel.plan.degree - 1)
        (sel.constant : ℚ_[sel.batch.primeAt j])
        (fun l => (sel.choice.coeff l : ℚ_[sel.batch.primeAt j])) := by
  have hcast (r : ℚ) : algebraMap ℚ ℚ_[sel.batch.primeAt j] r =
      (r : ℚ_[sel.batch.primeAt j]) := by
    simpa only [Rat.cast_id] using map_ratCast (algebraMap ℚ ℚ_[sel.batch.primeAt j]) r
  simp only [Selection.raw, ShiftedEisenstein.monicFamily_map, hcast]

theorem selection_word_derivative (sel : Selection R P) (j : sel.batch.indices)
    (w : Word n) (b : Bool) :
    (LocalInterpolation.wordDerivative
      (sel.raw.map (algebraMap ℚ ℚ_[sel.batch.primeAt j]))
      ((sel.plan.wordDen w).map (algebraMap ℚ ℚ_[sel.batch.primeAt j]))
      w.latestExponent (sel.batch.branch j b)).valuation < -((n + 1 : ℕ) : ℤ) := by
  rw [selection_raw_map]
  exact ((sel.choice.witnesses.2.2.2.2.2.1 j).2).2.1 w (Finset.mem_univ w) b

theorem batch_branch_nonzero (B : Batch) (j : B.indices) (b : Bool) :
    B.branch j b ≠ 0 := by
  intro h
  exact Polynomial.X_ne_zero ((transcendental_iff.mp (B.branch_transcendental j b))
    X (by simp [h]))

theorem batch_branch_integral (B : Batch) (j : B.indices) (b : Bool) :
    B.branch j b ∈ PadicInt.subring (B.primeAt j) := by
  cases b
  · exact (primary j.val).property
  · exact (B.guardAt j).value.property

theorem selection_wordDen_ne_zero (sel : Selection R P) (w : Word n) :
    sel.plan.wordDen w ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro j _
  exact pow_ne_zero _ (P.rawAt_monic j.val j.isLt).ne_zero

theorem selection_word_transfer (sel : Selection R P) (j : sel.batch.indices)
    (s : ℕ) (hs : s ≤ n + 1) (w : Word n) :
    ∃ U V : padicScaledPolynomialRing (sel.batch.primeAt j) s,
      (RatFunc.C (sel.batch.primeAt j : ℚ_[sel.batch.primeAt j]) ^ (2 * s) *
        ((RatFunc.X - RatFunc.C (sel.batch.branch j false)) *
          (RatFunc.X - RatFunc.C (sel.batch.branch j true)))) ^ w.latestExponent =
        RatFunc.C (sel.batch.primeAt j : ℚ_[sel.batch.primeAt j]) ^ (n + 1) *
          ((U : RatFunc ℚ_[sel.batch.primeAt j]) + (V : RatFunc ℚ_[sel.batch.primeAt j]) *
            ((sel.raw.map (algebraMap ℚ ℚ_[sel.batch.primeAt j]) : RatFunc ℚ_[sel.batch.primeAt j]) ^
              w.latestExponent /
                ((sel.plan.wordDen w).map (algebraMap ℚ ℚ_[sel.batch.primeAt j]) :
                  RatFunc ℚ_[sel.batch.primeAt j]))) := by
  rw [selection_raw_map]
  exact signed_word_transfer_in_padic_scaled_ring sel.batch.primeAt (fun _ => Fact.out)
    sel.choice.N (sel.batch.primeAt j) (sel.plan.degree - 1) (n + 1)
    (by have := sel.plan.large_degree; omega)
    (fun l => (sel.choice.coeff l : ℚ_[sel.batch.primeAt j]))
    (sel.batch.branch j) (sel.plan.denValue sel.batch.primeAt sel.batch.branch j)
    ((R.targets P sel.batch).value j) ((R.targets P sel.batch).precision j)
    (batch_branch_nonzero sel.batch j) (batch_branch_integral sel.batch j)
    Finset.univ (fun w => (sel.plan.wordDen w).map (algebraMap ℚ ℚ_[sel.batch.primeAt j]))
    RawWords.StageWord.latestExponent (sel.choice.witnesses.2.2.2.2.2.1 j).1
    (sel.choice.witnesses.2.2.2.2.2.1 j).2 s hs w (Finset.mem_univ w)
    w.latestExponent_bounds.1
    ((Polynomial.map_ne_zero_iff (algebraMap ℚ ℚ_[sel.batch.primeAt j]).injective).mpr
      (selection_wordDen_ne_zero sel w))


/-- The two permanent arguments attached to the same recursive sequence. -/
def branch (seq : Sequence R) (j : ℕ) (b : Bool) : ℚ_[(primes j).val] :=
  if b then (seq.chain.guardChain.value (primes j)).val else (primary j).val

theorem sequence_batch_eq_selection (seq : Sequence R) (n : ℕ) :
    seq.chain.batch n = (seq.selection n).batch := by
  rw [seq.chain.batch_eq_selected, seq.consistent]
  rfl

theorem selection_mem_indices (seq : Sequence R) (n j : ℕ)
    (hj : (primes j).val ≤ n + 1) : j ∈ (seq.selection n).batch.indices := by
  apply ((seq.selection n).batch.mem_indices j).mpr
  apply (seq.selection n).batch.covered
  apply (GuardStages.mem_primesThrough _ _).mpr
  exact hj.trans (seq.selection n).toNext.stage_cutoff

theorem selection_branch_eq (seq : Sequence R) (n : ℕ)
    (j : (seq.selection n).batch.indices) (b : Bool) :
    (seq.selection n).batch.branch j b = branch seq j.val b := by
  cases b with
  | false => rfl
  | true =>
    have hassign : seq.chain.guardChain.assignments n = (seq.selection n).batch.assigned := by
      rw [seq.chain.guardChain_assignments, sequence_batch_eq_selection]
    have hguard : ∀ hp : primes j.val ∈ (seq.selection n).batch.assigned.primes,
        ((seq.selection n).batch.assigned.guard (primes j.val) hp).value =
          seq.chain.guardChain.value (primes j.val) := by
      have hv := seq.chain.guardChain.value_agrees n (primes j.val)
      simpa only [hassign] using hv
    have hp := ((seq.selection n).batch.mem_indices j.val).mp j.property
    have he := hguard ((seq.selection n).batch.processed_subset_assigned hp)
    rw [(seq.selection n).batch.assigned_old (primes j.val) hp] at he
    exact congrArg Subtype.val he

/-- Every fixed prime occurs in all sufficiently late ordinary processing sets. -/
theorem eventually_mem_indices (seq : Sequence R) (j : ℕ) :
    ∀ᶠ n in atTop, j ∈ (seq.selection n).batch.indices := by
  filter_upwards [eventually_ge_atTop (primes j).val] with n hn
  exact selection_mem_indices seq n j (hn.trans (Nat.le_succ n))


set_option backward.isDefEq.respectTransparency false in
/-- Every fixed prime and scale eventually has all ordinary word-derivative
bounds and actual scaled-ring transfer identities for the same global raw sequence.
Raw stage n has the manuscript's positive arithmetic precision n+1. -/
theorem eventually_all_word_estimates (seq : Sequence R) (j s : ℕ) :
    ∀ᶠ n in atTop, ∀ w : Word n,
      (∀ b : Bool, (LocalInterpolation.wordDerivative
        ((seq.chain.raw n).map (algebraMap ℚ ℚ_[(primes j).val]))
        (((GlobalPlans.globalPlan seq n).wordDen w).map (algebraMap ℚ ℚ_[(primes j).val]))
        w.latestExponent (branch seq j b)).valuation < -((n + 1 : ℕ) : ℤ)) ∧
      ∃ U V : padicScaledPolynomialRing (primes j).val s,
        (RatFunc.C ((primes j).val : ℚ_[(primes j).val]) ^ (2 * s) *
          ((RatFunc.X - RatFunc.C (branch seq j false)) *
            (RatFunc.X - RatFunc.C (branch seq j true)))) ^ w.latestExponent =
          RatFunc.C ((primes j).val : ℚ_[(primes j).val]) ^ (n + 1) *
            ((U : RatFunc ℚ_[(primes j).val]) + (V : RatFunc ℚ_[(primes j).val]) *
              (((seq.chain.raw n).map (algebraMap ℚ ℚ_[(primes j).val]) :
                RatFunc ℚ_[(primes j).val]) ^ w.latestExponent /
                (((GlobalPlans.globalPlan seq n).wordDen w).map
                  (algebraMap ℚ ℚ_[(primes j).val]) : RatFunc ℚ_[(primes j).val]))) := by
  filter_upwards [eventually_mem_indices seq j, eventually_ge_atTop s] with n hj hs
  intro w
  constructor
  · intro b
    have h := selection_word_derivative (seq.selection n) ⟨j, hj⟩ w b
    simpa only [selection_branch_eq, Batch.primeAt, ← GlobalPlans.globalRaw_eq_selection,
      ← GlobalPlans.globalPlan_wordDen] using h
  · have h := selection_word_transfer (seq.selection n) ⟨j, hj⟩ s (by omega) w
    simpa only [selection_branch_eq, Batch.primeAt, ← GlobalPlans.globalRaw_eq_selection,
      ← GlobalPlans.globalPlan_wordDen] using h


theorem branch_transcendental (seq : Sequence R) (j : ℕ) (b : Bool) :
    Transcendental ℚ (branch seq j b) := by
  cases b
  · exact primary_transcendental j
  · exact seq.chain.guardChain.value_transcendental (primes j)

theorem branch_integral (seq : Sequence R) (j : ℕ) (b : Bool) :
    branch seq j b ∈ PadicInt.subring (primes j).val := by
  cases b
  · exact (primary j).property
  · exact (seq.chain.guardChain.value (primes j)).property

theorem branch_ne (seq : Sequence R) (j : ℕ) : branch seq j false ≠ branch seq j true := by
  intro heq
  have he : primary j = seq.chain.guardChain.value (primes j) := Subtype.ext heq
  exact primary_not_unit j (he ▸ seq.chain.guardChain.value_unit (primes j))

theorem raw_eval_ne_zero (seq : Sequence R) (n j : ℕ) (b : Bool) :
    (seq.chain.raw n).eval₂ (algebraMap ℚ ℚ_[(primes j).val]) (branch seq j b) ≠ 0 := by
  intro h
  exact (seq.chain.raw_monic n).ne_zero ((transcendental_iff.mp
    (branch_transcendental seq j b)) (seq.chain.raw n) h)

theorem global_wordDen_eval_ne_zero (seq : Sequence R) (n : ℕ) (w : Word n)
    (j : ℕ) (b : Bool) :
    ((GlobalPlans.globalPlan seq n).wordDen w).eval₂
      (algebraMap ℚ ℚ_[(primes j).val]) (branch seq j b) ≠ 0 := by
  rw [← eval_map]
  exact old_product_eval_ne_zero_of_transcendental n seq.chain.raw
    (fun k _ => seq.chain.raw_monic k) ((GlobalPlans.globalPlan seq n).powers w)
    (branch seq j b) (branch_transcendental seq j b)

end UnconditionalCounterexample.SequenceLocalTransfer
