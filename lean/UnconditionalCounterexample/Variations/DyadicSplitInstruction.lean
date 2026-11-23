import UnconditionalCounterexample.Variations.DyadicDispatch
import UnconditionalCounterexample.Variations.DyadicSplitCoefficients

/-!
# Evaluating a split instruction against the ledger's actual prefix

Old exponents are read from the chronological history of selected labels.
The ledger and the finite polynomial prefix therefore suffice to compute the
unit targets at the reserved stage.
-/

noncomputable section
namespace UnconditionalCounterexample.Variations.DyadicLedger

open RecursivePrefix Univariate

namespace Driver

variable (D : Driver)

theorem instruction_prefix_eq (I : SplitInstruction) (n : ℕ) :
    I.prefix (D.state n) ((chain D.requirements).approx n) =
      DyadicSplit.prefixFactor ((chain D.requirements).approx n) I.coarse
        (fun j => I.coefficients (D.actualRequest j).column) := by
  unfold SplitInstruction.prefix DyadicSplit.prefixFactor
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  simp [D.raw_history n, List.getElem?_range (Finset.mem_range.mp hj)]

/-- The stored prefix factor and the selected normalized raw at its own
reserved stage multiply to the full signed expression of the instruction. -/
theorem instruction_mul_reserved (I : SplitInstruction) (n : ℕ) (w : RawColumn → (RatFunc ℚ)ˣ)
    (hfrozen : I.coefficients.support ⊆ (Finset.range (n+1)).image (fun j => (D.actualRequest j).column))
    (hdistinct : Set.InjOn (fun j => (D.actualRequest j).column) ↑(Finset.range (n+1)))
    (hgen : ∀ j ≤ n, w (D.actualRequest j).column =
      Units.mk0 ((chain D.requirements).generators j) ((chain D.requirements).generators_ne_zero j))
    (hlast : (D.actualRequest n).column = .balanced I.channel I.index) :
    I.prefix (D.state n) ((chain D.requirements).approx n) *
      Units.mk0 ((chain D.requirements).generators n) ((chain D.requirements).generators_ne_zero n) =
        I.coarse * DyadicSplit.weightedProduct w I.coefficients := by
  rw [D.instruction_prefix_eq]
  exact DyadicSplit.prefixFactor_mul_reserved _ n _ _ _ w hfrozen hdistinct hgen (hlast ▸ I.exponent_one)

/-- Read a label from the selected stages through `n`. A value outside their
image is unused by every word supported in this prefix. -/
def wordValueThrough (n : ℕ) (c : RawColumn) : (RatFunc ℚ)ˣ := by
  classical
  exact if h : ∃ j ≤ n, (D.actualRequest j).column = c then
    Units.mk0 ((chain D.requirements).generators h.choose) ((chain D.requirements).generators_ne_zero _)
  else 1

theorem wordValueThrough_eq (n : ℕ)
    (hdistinct : Set.InjOn (fun j => (D.actualRequest j).column) ↑(Finset.range (n+1)))
    (j : ℕ) (hj : j ≤ n) :
    D.wordValueThrough n (D.actualRequest j).column =
      Units.mk0 ((chain D.requirements).generators j) ((chain D.requirements).generators_ne_zero j) := by
  have h : ∃ i ≤ n, (D.actualRequest i).column = (D.actualRequest j).column := ⟨j,hj,rfl⟩
  have ht : h.choose = j := hdistinct (Finset.mem_range.mpr (by have := h.choose_spec.1; omega))
    (Finset.mem_range.mpr (by omega)) h.choose_spec.2
  simp [wordValueThrough,h,ht]

open DyadicDeviations

/-- The factor actually selected in the recursion realizes the signed split
profile. The hypotheses on generator valuations are restricted to the finitely
many stages used by this split. -/
theorem instruction_profile {J : Bool → Type*} {G H : Type*}
    (prime : (Σ k, J k) ↪ GuardSupport.PrimeIndex) (index : (k : Bool) → J k → ℕ)
    (positive : (k : Bool) → J k → Bool) (sign : (k : Bool) → J k → ℤ)
    (signed : (RatFunc ℚ)ˣ → Profile J G H) (I : SplitInstruction) (n : ℕ)
    (u : Profile J G H)
    (htarget : (signed I.coarse).translate index sign (columnsOfRaw prime index positive I.coefficients) = u)
    (hfrozen : I.coefficients.support ⊆ (Finset.range (n+1)).image (fun j => (D.actualRequest j).column))
    (hdistinct : Set.InjOn (fun j => (D.actualRequest j).column) ↑(Finset.range (n+1)))
    (hlast : (D.actualRequest n).column = .balanced I.channel I.index)
    (hraw : ∀ j ≤ n, (D.actualRequest j).column ∈ I.coefficients.support → ∀ y,
      signed (y * Units.mk0 ((chain D.requirements).generators j) ((chain D.requirements).generators_ne_zero j)) =
        (signed y).translate index sign
          (columnsOfRaw prime index positive (Finsupp.single (D.actualRequest j).column 1))) :
    signed (I.prefix (D.state n) ((chain D.requirements).approx n) *
      Units.mk0 ((chain D.requirements).generators n) ((chain D.requirements).generators_ne_zero n)) = u := by
  rw [D.instruction_mul_reserved I n (D.wordValueThrough n) hfrozen hdistinct
    (D.wordValueThrough_eq n hdistinct) hlast]
  apply splitWord_profile prime index positive sign signed _ _ _ _ htarget
  intro c hc
  obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp (hfrozen hc)
  have hj' : j ≤ n := by simpa using hj
  rw [D.wordValueThrough_eq n hdistinct j hj']
  exact hraw j hj' hc

end Driver
end UnconditionalCounterexample.Variations.DyadicLedger
