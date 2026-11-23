import UnconditionalCounterexample.Variations.UnivariateSelection
import UnconditionalCounterexample.PaperConstruction

/-!
# The original polynomial sequence as a one-centre client

Reinterpret the actual coefficient choices and arguments from the paper
construction as mixed choices. No new polynomial is selected.
-/

noncomputable section
namespace UnconditionalCounterexample.Variations.Univariate

open Polynomial GuardSupport PrimaryChoices CombinedGuardStep ConstructionWords

def originalSite (B : Batch) (i : B.indices) : Site (primes i.val) where
  guard := (B.guardAt i).value
  guard_trans := (B.guardAt i).transcendental
  primary := some ⟨primary i.val, primary_transcendental i.val, by
    have hzero : PadicInt.toZMod (primary i.val) = 0 := by
      by_contra h
      exact primary_not_unit i.val ((padicInt_isUnit_iff_toZMod_ne_zero _).mpr h)
    rw [hzero]
    exact ((padicInt_isUnit_iff_toZMod_ne_zero _).mp (B.guardAt i).unit).symm⟩

@[simp] theorem originalSite_paired (B : Batch) (i : B.indices) : (originalSite B i).paired := rfl

theorem originalSite_branch (B : Batch) (i : B.indices) :
    (originalSite B i).branch = B.branch i := by
  funext b
  cases b <;> rfl

/-- The all-paired selector embeds into the mixed selector with the same
clearing powers, coefficients, local estimates and Eisenstein model. -/
def mixedChoiceOfOriginal {n : ℕ} {P : ℕ → ℚ[X]} {oldE : ℕ → ℕ}
    {ι : Type*} [Fintype ι] {p : ι → ℕ} [∀ i, Fact (p i).Prime]
    {ell : ℕ} [Fact ell.Prime] {plan : DegreePlan n P oldE}
    {x v : ∀ i, Bool → ℚ_[p i]} {kv : ι → Bool → ℕ}
    (c : Choice p ell plan x v kv) :
    MixedConstructionWords.Choice p (fun _ => True) ell plan x v kv where
  N := c.N
  coeff := c.coeff
  positive_multiple := c.positive_multiple
  witnesses := by
    obtain ⟨hm, hd, hc, hi, hs, hl, hg, he⟩ := c.witnesses
    refine ⟨hm, hd, hc, hi, hs, ?_, hg, he⟩
    intro i
    obtain ⟨hclear, htarget, hderiv, hcoeff⟩ := hl i
    simp only [MixedStageSelection.fixedRemainder, MixedStageSelection.localTarget, ite_true]
    exact ⟨hclear, fun b _ => htarget b, fun w hw b _ => hderiv w hw b, hcoeff⟩

/-- At each original stage the actual finite choice, expressed in mixed coordinates
at the original sites, has literally the coefficients and signed exponents of
the polynomial appended by the paper construction. -/
theorem original_choice (n : ℕ) :
    let s := PaperConstruction.construction.selection n
    let t := PaperConstruction.targets (PaperConstruction.construction.chain.approx n) s.batch
    ∃ c : MixedConstructionWords.Choice s.batch.primeAt (fun j => (originalSite s.batch j).paired)
      s.batch.auxiliary.val s.plan (fun j => (originalSite s.batch j).branch) t.value t.precision,
      c.N = s.choice.N ∧ c.coeff = s.choice.coeff ∧
      PaperConstruction.raw n =
        ShiftedEisenstein.monicFamily (s.plan.degree - 1)
          (SignedConstant.constant s.batch.primeAt c.N (s.plan.degree - 1 + 1)) c.coeff := by
  intro s t
  have hp : (fun j => (originalSite s.batch j).paired) = (fun _ => True) := by
    funext j
    exact propext ⟨fun _ => trivial, fun _ => originalSite_paired _ _⟩
  have hx : (fun j => (originalSite s.batch j).branch) = s.batch.branch :=
    funext (originalSite_branch s.batch)
  rw [hp, hx]
  refine ⟨mixedChoiceOfOriginal s.choice, rfl, rfl, ?_⟩
  change PaperConstruction.construction.chain.raw n = s.raw
  exact (PaperConstruction.construction.chain.raw_eq_selected n).trans
    (congrArg RecursivePrefix.Next.raw (PaperConstruction.construction.consistent n))

end UnconditionalCounterexample.Variations.Univariate
