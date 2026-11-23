import UnconditionalCounterexample.Variations.PrivateGuardsMainStage
import UnconditionalCounterexample.Variations.PrivateGuardsChronology
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Main-stage policies for the live private-guard recursion

The arithmetic, geometric and derivative tests may depend on the entire
completed history. The unit-return policy gives one explicit unconditional
instance whose private values approach one.
-/

noncomputable section
namespace UnconditionalCounterexample.Variations.PrivateGuards.Live

open MvPolynomial GuardSupport MultivariateSelection
open scoped Topology

variable {r n : ℕ} {M : ℕ → Type*} {k : Type*} [Field k] [CharZero k]

structure Prescription (k : Type*) [Field k] (h : History r M n) where
  memory : M n
  reg : Finset PrimeIndex
  blocked : Finset PrimeIndex
  separate : ∀ j, (h j).prime ∉ reg
  floor : ℕ
  regular : ∀ d > floor, ∀ v : reg, OpenLower r d v.val
  pairs : (j : Fin n) → PairTests (h j)
  geometry : Finset (MultivariateStage.Test k (Fin (r+1)))
  valid : ∀ t ∈ geometry, t.Valid

namespace Prescription
variable {h : History r M n}

def Satisfied (P : Prescription k h) (x : MainChoice r n (M n)) : Prop :=
  P.floor < x.entry.degree ∧ x.entry.memory = P.memory ∧
  (x.entry.raw n).totalDegree = x.entry.degree ∧
  (∀ j, (P.pairs j).Holds (oldDenominator h) (MvPolynomial.map (algebraMap ℚ ℚ_[(h j).prime.val]) (x.entry.raw n))) ∧
  (∀ v : P.reg, ∃ hd : P.floor < x.entry.degree,
    (fun m => ((x.entry.lower.coeff m : ℚ) : ℚ_[v.val.val])) ∈ (P.regular x.entry.degree hd v).neighborhood) ∧
  (∀ t ∈ P.geometry, t.Holds (MvPolynomial.map (algebraMap ℚ k) (x.entry.raw n))) ∧
  (∀ j, (h j).prime ∈ x.reserved) ∧ P.reg ⊆ x.reserved ∧ P.blocked ⊆ x.reserved ∧
  (∃ ell ∈ x.reserved, ell ∉ P.reg ∧ (∀ j, ell ≠ (h j).prime) ∧
    ∀ m, HasAuxiliaryResidue ell.val (x.entry.lower.coeff m)
      (if m = 0 then (ell.val : ZMod (ell.val^2)) else 0)) ∧
  ∀ m p, p.Prime → p ∣ (x.entry.lower.coeff m).den → (∃ v : P.reg, p = v.val.val) ∨ ∃ j, p = (h j).prime.val

end Prescription

def ruleOf (c : Fin (r+1) → ℚ) (P : ∀ n (h : History r M n), Prescription k h) : Rule r M c where
  Accepts n h x := (P n h).Satisfied x
  produces n h hinj := by
    let u := P n h
    obtain ⟨x,hfl,hm,hdeg,hc,hunit,hrest⟩ := exists_main_stage h
      (fun _ _ he ↦ hinj (congrArg Subtype.val he)) u.memory u.reg u.blocked u.separate
      u.floor u.regular u.pairs c u.geometry u.valid
    exact ⟨x,hc,hunit,hfl,hm,hdeg,hrest⟩

def unitReturnTests (s : Round r n (M n)) (stage : ℕ) : PairTests s where
  target _ := 1
  target_unit _ := norm_one
  idealGenerator := 0
  vanishes _ := map_zero _
  words := 0
  denominator := Fin.elim0
  exponent := Fin.elim0
  positive j := Fin.elim0 j
  avoids _ j := Fin.elim0 j
  observations := 0
  observation := Fin.elim0
  precision := 1 / ((stage : ℝ)+1)
  precision_pos := by positivity
  minScale := stage

def unitReturnPrescription (n : ℕ) (h : History r (fun _ => Unit) n) : Prescription ℚ h where
  memory := ()
  reg := ∅
  blocked := ∅
  separate _ := Finset.notMem_empty _
  floor := max n (Finset.univ.sup (fun j : Fin n ↦ (h j).entry.degree))
  regular _ _ v := (Finset.notMem_empty _ v.property).elim
  pairs j := unitReturnTests (M := fun _ => Unit) (n := j.val) (h j) n
  geometry := ∅
  valid _ ht := (Finset.notMem_empty _ ht).elim

def unitReturnRule (c : Fin (r+1) → ℚ) : Rule r (fun _ => Unit) c := ruleOf c unitReturnPrescription

theorem unitReturnRule_estimate (c : Fin (r+1) → ℚ) (h : History r (fun _ => Unit) n)
    {x : MainChoice r n Unit} (hx : (unitReturnRule c).Accepts n h x)
    (j : Fin n) (b : Bool) :
    ‖aeval ((h j).pair.point b) (x.entry.raw n) / aeval ((h j).pair.point b) (oldDenominator h) - 1‖ <
      1 / ((n : ℝ)+1) := by
  have hi := (hx.2.2.2.1 j).1 b
  simpa [aeval_map_algebraMap, unitReturnPrescription, unitReturnTests] using hi.2

theorem unitReturnPrecision_tendsto : Filter.Tendsto (fun n : ℕ ↦ 1 / ((n : ℝ)+1))
    Filter.atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat

end UnconditionalCounterexample.Variations.PrivateGuards.Live
