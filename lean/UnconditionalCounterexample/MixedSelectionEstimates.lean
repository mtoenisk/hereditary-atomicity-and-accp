import UnconditionalCounterexample.MixedGlobalPlans
import UnconditionalCounterexample.MixedWordTransfer

/-! # Local estimates for the selected stage polynomial at each active branch -/

noncomputable section
namespace UnconditionalCounterexample.MixedLocalTransfer
open Polynomial Filter ConstructionWords MixedStageRecursion CombinedGuardStep
open PrimaryChoices GuardSupport LocalAlgebra MixedStageSelection MixedWordTransfer

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
    (w : Word n) (b : Bool) (hb : Active (R.primary.paired (primes j.val)) b) :
    (LocalInterpolation.wordDerivative
      (sel.raw.map (algebraMap ℚ ℚ_[sel.batch.primeAt j]))
      ((sel.plan.wordDen w).map (algebraMap ℚ ℚ_[sel.batch.primeAt j]))
      w.latestExponent (R.primary.branch sel.batch j b)).valuation < -((n + 1 : ℕ) : ℤ) := by
  rw [selection_raw_map]
  exact ((sel.choice.witnesses.2.2.2.2.2.1 j).2).2.1 w (Finset.mem_univ w) b hb

private theorem batch_nonzero (B : Batch) (j : B.indices) (b : Bool)
    (hb : Active (R.primary.paired (primes j.val)) b) : R.primary.branch B j b ≠ 0 :=
  (R.primary.branch_transcendental B j b hb).ne_zero

private theorem batch_integral (B : Batch) (j : B.indices) (b : Bool)
    (hb : Active (R.primary.paired (primes j.val)) b) :
    R.primary.branch B j b ∈ PadicInt.subring (B.primeAt j) := by
  cases b with
  | true => exact (B.guardAt j).value.property
  | false =>
    have h := hb.resolve_left (by decide)
    rw [PrimaryData.branch_false _ B j h]
    exact (R.primary.value _ h).property

theorem selection_wordDen_ne_zero (sel : Selection R P) (w : Word n) :
    sel.plan.wordDen w ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro j _
  exact pow_ne_zero _ (P.rawAt_monic j.val j.isLt).ne_zero

theorem selection_word_transfer (sel : Selection R P) (j : sel.batch.indices)
    (s : ℕ) (hs : s ≤ n + 1) (w : Word n) :
    ∃ U V : padicScaledPolynomialRing (sel.batch.primeAt j) s,
      (RatFunc.C (sel.batch.primeAt j : ℚ_[sel.batch.primeAt j]) ^ (2 * s) *
        (vanishing (R.primary.paired (primes j.val)) (R.primary.branch sel.batch j))) ^ w.latestExponent =
        RatFunc.C (sel.batch.primeAt j : ℚ_[sel.batch.primeAt j]) ^ (n + 1) *
          ((U : RatFunc ℚ_[sel.batch.primeAt j]) + (V : RatFunc ℚ_[sel.batch.primeAt j]) *
            ((sel.raw.map (algebraMap ℚ ℚ_[sel.batch.primeAt j]) : RatFunc ℚ_[sel.batch.primeAt j]) ^
              w.latestExponent /
                ((sel.plan.wordDen w).map (algebraMap ℚ ℚ_[sel.batch.primeAt j]) :
                  RatFunc ℚ_[sel.batch.primeAt j]))) := by
  rw [selection_raw_map]
  exact signed_transfer sel.batch.primeAt (fun _ => Fact.out)
    sel.choice.N (sel.batch.primeAt j) (R.primary.paired (primes j.val)) (sel.plan.degree - 1) (n + 1)
    (by have := sel.plan.large_degree; omega)
    (fun l => (sel.choice.coeff l : ℚ_[sel.batch.primeAt j]))
    (R.primary.branch sel.batch j) (sel.plan.denValue sel.batch.primeAt (R.primary.branch sel.batch) j)
    ((R.targets P sel.batch).value j) ((R.targets P sel.batch).precision j)
    (batch_nonzero sel.batch j) (batch_integral sel.batch j)
    Finset.univ (fun w => (sel.plan.wordDen w).map (algebraMap ℚ ℚ_[sel.batch.primeAt j]))
    RawWords.StageWord.latestExponent (sel.choice.witnesses.2.2.2.2.2.1 j).1
    (sel.choice.witnesses.2.2.2.2.2.1 j).2 s hs w (Finset.mem_univ w)
    w.latestExponent_bounds.1
    ((Polynomial.map_ne_zero_iff (algebraMap ℚ ℚ_[sel.batch.primeAt j]).injective).mpr
      (selection_wordDen_ne_zero sel w))


end UnconditionalCounterexample.MixedLocalTransfer
